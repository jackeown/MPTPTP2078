%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 200 expanded)
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

tff(f_84,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(c_32,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_orders_2(A_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),u1_struct_0(A_31))))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_34] :
      ( v1_relat_1(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_28,plain,(
    r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( r1_relat_2(A_20,B_21)
      | ~ r3_orders_1(A_20,B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_51,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_84,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_51])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_84])).

tff(c_90,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( r6_relat_2(A_7,B_9)
      | ~ r3_orders_1(A_7,B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_89,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r7_relat_2(B_12,A_11)
      | ~ r6_relat_2(B_12,A_11)
      | ~ r1_relat_2(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_108,plain,(
    ! [B_45,A_46] :
      ( v6_orders_2(B_45,A_46)
      | ~ r7_relat_2(u1_orders_2(A_46),B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_111,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_114,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_111])).

tff(c_115,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_114])).

tff(c_118,plain,
    ( ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_121,plain,(
    ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_118])).

tff(c_124,plain,
    ( ~ r3_orders_1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_28,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.04/1.23  
% 2.04/1.23  %Foreground sorts:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Background operators:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Foreground operators:
% 2.04/1.23  tff(r3_orders_1, type, r3_orders_1: ($i * $i) > $o).
% 2.04/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.23  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.04/1.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.23  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.04/1.23  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.04/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.04/1.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.04/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.23  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.23  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.04/1.23  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.04/1.23  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.04/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.23  
% 2.13/1.24  tff(f_84, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r3_orders_1(u1_orders_2(A), B) => (v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_orders_2)).
% 2.13/1.24  tff(f_55, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.13/1.24  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.13/1.24  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r3_orders_1(A, B) <=> (((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_orders_1)).
% 2.13/1.24  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_orders_1)).
% 2.13/1.24  tff(f_38, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 2.13/1.24  tff(c_32, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.24  tff(c_64, plain, (![A_31]: (m1_subset_1(u1_orders_2(A_31), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), u1_struct_0(A_31)))) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.24  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.24  tff(c_81, plain, (![A_34]: (v1_relat_1(u1_orders_2(A_34)) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_64, c_2])).
% 2.13/1.24  tff(c_28, plain, (r3_orders_1(u1_orders_2('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.24  tff(c_46, plain, (![A_20, B_21]: (r1_relat_2(A_20, B_21) | ~r3_orders_1(A_20, B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.24  tff(c_50, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.13/1.24  tff(c_51, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.13/1.24  tff(c_84, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_81, c_51])).
% 2.13/1.24  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_84])).
% 2.13/1.24  tff(c_90, plain, (v1_relat_1(u1_orders_2('#skF_1'))), inference(splitRight, [status(thm)], [c_50])).
% 2.13/1.24  tff(c_10, plain, (![A_7, B_9]: (r6_relat_2(A_7, B_9) | ~r3_orders_1(A_7, B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.24  tff(c_89, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 2.13/1.24  tff(c_20, plain, (![B_12, A_11]: (r7_relat_2(B_12, A_11) | ~r6_relat_2(B_12, A_11) | ~r1_relat_2(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.24  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.24  tff(c_26, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.24  tff(c_42, plain, (~v6_orders_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 2.13/1.24  tff(c_108, plain, (![B_45, A_46]: (v6_orders_2(B_45, A_46) | ~r7_relat_2(u1_orders_2(A_46), B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.24  tff(c_111, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_30, c_108])).
% 2.13/1.24  tff(c_114, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_111])).
% 2.13/1.24  tff(c_115, plain, (~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_114])).
% 2.13/1.24  tff(c_118, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_115])).
% 2.13/1.24  tff(c_121, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_89, c_118])).
% 2.13/1.24  tff(c_124, plain, (~r3_orders_1(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_121])).
% 2.13/1.24  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_28, c_124])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 13
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 1
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 1
% 2.13/1.24  #Demod        : 8
% 2.13/1.24  #Tautology    : 4
% 2.13/1.24  #SimpNegUnit  : 2
% 2.13/1.24  #BackRed      : 0
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.25  Preprocessing        : 0.31
% 2.13/1.25  Parsing              : 0.17
% 2.13/1.25  CNF conversion       : 0.02
% 2.13/1.25  Main loop            : 0.16
% 2.13/1.25  Inferencing          : 0.07
% 2.13/1.25  Reduction            : 0.04
% 2.13/1.25  Demodulation         : 0.03
% 2.13/1.25  BG Simplification    : 0.01
% 2.13/1.25  Subsumption          : 0.02
% 2.13/1.25  Abstraction          : 0.01
% 2.13/1.25  MUC search           : 0.00
% 2.13/1.25  Cooper               : 0.00
% 2.13/1.25  Total                : 0.50
% 2.13/1.25  Index Insertion      : 0.00
% 2.13/1.25  Index Deletion       : 0.00
% 2.13/1.25  Index Matching       : 0.00
% 2.13/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
