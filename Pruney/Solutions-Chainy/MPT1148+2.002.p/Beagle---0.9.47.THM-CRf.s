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

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   56 (  86 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 191 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_wellord1(u1_orders_2(A),B)
             => ( v6_orders_2(B,A)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_orders_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
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

tff(f_49,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(c_36,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_36] :
      ( m1_subset_1(u1_orders_2(A_36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(A_36))))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_36] :
      ( v1_relat_1(u1_orders_2(A_36))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(A_36)))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_90,plain,(
    ! [A_39] :
      ( v1_relat_1(u1_orders_2(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_32,plain,(
    r2_wellord1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    ! [A_18,B_19] :
      ( r1_wellord1(A_18,B_19)
      | ~ r2_wellord1(A_18,B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,
    ( r1_wellord1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_45,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_93,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_45])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_99,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_10,plain,(
    ! [A_6,B_8] :
      ( r6_relat_2(A_6,B_8)
      | ~ r2_wellord1(A_6,B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_42,B_43] :
      ( r1_relat_2(A_42,B_43)
      | ~ r2_wellord1(A_42,B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_107,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_104])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r7_relat_2(B_14,A_13)
      | ~ r6_relat_2(B_14,A_13)
      | ~ r1_relat_2(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_142,plain,(
    ! [B_60,A_61] :
      ( v6_orders_2(B_60,A_61)
      | ~ r7_relat_2(u1_orders_2(A_61),B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_148,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_145])).

tff(c_149,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_148])).

tff(c_152,plain,
    ( ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_149])).

tff(c_155,plain,(
    ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_107,c_152])).

tff(c_158,plain,
    ( ~ r2_wellord1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_32,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.04/1.22  
% 2.04/1.22  %Foreground sorts:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Background operators:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Foreground operators:
% 2.04/1.22  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.04/1.22  tff(r1_wellord1, type, r1_wellord1: ($i * $i) > $o).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.22  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.04/1.22  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.04/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.22  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.04/1.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.22  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.22  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.04/1.22  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.04/1.22  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.04/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.22  
% 2.17/1.23  tff(f_82, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_wellord1(u1_orders_2(A), B) => (v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_orders_2)).
% 2.17/1.23  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.23  tff(f_62, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.17/1.23  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.23  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_wellord1(A, B) <=> ((((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)) & r1_wellord1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_wellord1)).
% 2.17/1.23  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_orders_1)).
% 2.17/1.23  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 2.17/1.23  tff(c_36, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.23  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.23  tff(c_71, plain, (![A_36]: (m1_subset_1(u1_orders_2(A_36), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36), u1_struct_0(A_36)))) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.23  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.23  tff(c_74, plain, (![A_36]: (v1_relat_1(u1_orders_2(A_36)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_36), u1_struct_0(A_36))) | ~l1_orders_2(A_36))), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.17/1.23  tff(c_90, plain, (![A_39]: (v1_relat_1(u1_orders_2(A_39)) | ~l1_orders_2(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_74])).
% 2.17/1.23  tff(c_32, plain, (r2_wellord1(u1_orders_2('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.23  tff(c_40, plain, (![A_18, B_19]: (r1_wellord1(A_18, B_19) | ~r2_wellord1(A_18, B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.23  tff(c_44, plain, (r1_wellord1(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_40])).
% 2.17/1.23  tff(c_45, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.17/1.23  tff(c_93, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_90, c_45])).
% 2.17/1.23  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 2.17/1.23  tff(c_99, plain, (v1_relat_1(u1_orders_2('#skF_1'))), inference(splitRight, [status(thm)], [c_44])).
% 2.17/1.23  tff(c_10, plain, (![A_6, B_8]: (r6_relat_2(A_6, B_8) | ~r2_wellord1(A_6, B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.23  tff(c_101, plain, (![A_42, B_43]: (r1_relat_2(A_42, B_43) | ~r2_wellord1(A_42, B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.23  tff(c_104, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_101])).
% 2.17/1.23  tff(c_107, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_104])).
% 2.17/1.23  tff(c_24, plain, (![B_14, A_13]: (r7_relat_2(B_14, A_13) | ~r6_relat_2(B_14, A_13) | ~r1_relat_2(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.23  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.23  tff(c_30, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.23  tff(c_38, plain, (~v6_orders_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 2.17/1.23  tff(c_142, plain, (![B_60, A_61]: (v6_orders_2(B_60, A_61) | ~r7_relat_2(u1_orders_2(A_61), B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.23  tff(c_145, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_34, c_142])).
% 2.17/1.23  tff(c_148, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_145])).
% 2.17/1.23  tff(c_149, plain, (~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_148])).
% 2.17/1.23  tff(c_152, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_149])).
% 2.17/1.23  tff(c_155, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_107, c_152])).
% 2.17/1.23  tff(c_158, plain, (~r2_wellord1(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_155])).
% 2.17/1.23  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_32, c_158])).
% 2.17/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.23  
% 2.17/1.23  Inference rules
% 2.17/1.23  ----------------------
% 2.17/1.23  #Ref     : 0
% 2.17/1.23  #Sup     : 18
% 2.17/1.23  #Fact    : 0
% 2.17/1.23  #Define  : 0
% 2.17/1.23  #Split   : 3
% 2.17/1.23  #Chain   : 0
% 2.17/1.23  #Close   : 0
% 2.17/1.23  
% 2.17/1.23  Ordering : KBO
% 2.17/1.23  
% 2.17/1.23  Simplification rules
% 2.17/1.23  ----------------------
% 2.17/1.23  #Subsume      : 3
% 2.17/1.23  #Demod        : 12
% 2.17/1.23  #Tautology    : 4
% 2.17/1.23  #SimpNegUnit  : 2
% 2.17/1.23  #BackRed      : 0
% 2.17/1.23  
% 2.17/1.23  #Partial instantiations: 0
% 2.17/1.23  #Strategies tried      : 1
% 2.17/1.23  
% 2.17/1.23  Timing (in seconds)
% 2.17/1.23  ----------------------
% 2.17/1.24  Preprocessing        : 0.29
% 2.17/1.24  Parsing              : 0.16
% 2.17/1.24  CNF conversion       : 0.02
% 2.17/1.24  Main loop            : 0.18
% 2.17/1.24  Inferencing          : 0.08
% 2.17/1.24  Reduction            : 0.05
% 2.17/1.24  Demodulation         : 0.03
% 2.17/1.24  BG Simplification    : 0.01
% 2.17/1.24  Subsumption          : 0.02
% 2.17/1.24  Abstraction          : 0.01
% 2.17/1.24  MUC search           : 0.00
% 2.17/1.24  Cooper               : 0.00
% 2.17/1.24  Total                : 0.50
% 2.17/1.24  Index Insertion      : 0.00
% 2.17/1.24  Index Deletion       : 0.00
% 2.17/1.24  Index Matching       : 0.00
% 2.17/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
