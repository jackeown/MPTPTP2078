%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   46 (  74 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_67,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r7_relat_2(C,A)
          & r1_tarski(B,A) )
       => r7_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_orders_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ~ v6_orders_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12])).

tff(c_22,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [B_26,A_27] :
      ( v6_orders_2(B_26,A_27)
      | ~ r7_relat_2(u1_orders_2(A_27),B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,
    ( v6_orders_2('#skF_3','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_76,plain,
    ( v6_orders_2('#skF_3','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_70])).

tff(c_77,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_76])).

tff(c_26,plain,(
    ! [A_18] :
      ( m1_subset_1(u1_orders_2(A_18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18),u1_struct_0(A_18))))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_relat_1(u1_orders_2(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_20,plain,(
    v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_37,plain,(
    ! [A_24,B_25] :
      ( r7_relat_2(u1_orders_2(A_24),B_25)
      | ~ v6_orders_2(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v6_orders_2('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_37])).

tff(c_46,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_40])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [C_20,B_21,A_22] :
      ( r7_relat_2(C_20,B_21)
      | ~ r1_tarski(B_21,A_22)
      | ~ r7_relat_2(C_20,A_22)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    ! [C_20] :
      ( r7_relat_2(C_20,'#skF_3')
      | ~ r7_relat_2(C_20,'#skF_2')
      | ~ v1_relat_1(C_20) ) ),
    inference(resolution,[status(thm)],[c_14,c_32])).

tff(c_53,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_35])).

tff(c_54,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_57,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_57])).

tff(c_62,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  %$ v6_orders_2 > r7_relat_2 > r1_tarski > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.16  
% 1.79/1.16  %Foreground sorts:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Background operators:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Foreground operators:
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.16  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.16  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 1.79/1.16  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.79/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.79/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.16  
% 1.79/1.18  tff(f_67, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: ((v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_orders_2)).
% 1.79/1.18  tff(f_38, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 1.79/1.18  tff(f_42, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 1.79/1.18  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.79/1.18  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => ((r7_relat_2(C, A) & r1_tarski(B, A)) => r7_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_orders_1)).
% 1.79/1.18  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_12, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v6_orders_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_24, plain, (~v6_orders_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12])).
% 1.79/1.18  tff(c_22, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_64, plain, (![B_26, A_27]: (v6_orders_2(B_26, A_27) | ~r7_relat_2(u1_orders_2(A_27), B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.18  tff(c_70, plain, (v6_orders_2('#skF_3', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_3') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_64])).
% 1.79/1.18  tff(c_76, plain, (v6_orders_2('#skF_3', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_70])).
% 1.79/1.18  tff(c_77, plain, (~r7_relat_2(u1_orders_2('#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24, c_76])).
% 1.79/1.18  tff(c_26, plain, (![A_18]: (m1_subset_1(u1_orders_2(A_18), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18), u1_struct_0(A_18)))) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.18  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.18  tff(c_30, plain, (![A_18]: (v1_relat_1(u1_orders_2(A_18)) | ~l1_orders_2(A_18))), inference(resolution, [status(thm)], [c_26, c_2])).
% 1.79/1.18  tff(c_20, plain, (v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_37, plain, (![A_24, B_25]: (r7_relat_2(u1_orders_2(A_24), B_25) | ~v6_orders_2(B_25, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.18  tff(c_40, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v6_orders_2('#skF_2', '#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_18, c_37])).
% 1.79/1.18  tff(c_46, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_40])).
% 1.79/1.18  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_32, plain, (![C_20, B_21, A_22]: (r7_relat_2(C_20, B_21) | ~r1_tarski(B_21, A_22) | ~r7_relat_2(C_20, A_22) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.18  tff(c_35, plain, (![C_20]: (r7_relat_2(C_20, '#skF_3') | ~r7_relat_2(C_20, '#skF_2') | ~v1_relat_1(C_20))), inference(resolution, [status(thm)], [c_14, c_32])).
% 1.79/1.18  tff(c_53, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_35])).
% 1.79/1.18  tff(c_54, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_53])).
% 1.79/1.18  tff(c_57, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_30, c_54])).
% 1.79/1.18  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_57])).
% 1.79/1.18  tff(c_62, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_53])).
% 1.79/1.18  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_62])).
% 1.79/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  Inference rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Ref     : 0
% 1.79/1.18  #Sup     : 8
% 1.79/1.18  #Fact    : 0
% 1.79/1.18  #Define  : 0
% 1.79/1.18  #Split   : 1
% 1.79/1.18  #Chain   : 0
% 1.79/1.18  #Close   : 0
% 1.79/1.18  
% 1.79/1.18  Ordering : KBO
% 1.79/1.18  
% 1.79/1.18  Simplification rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Subsume      : 1
% 1.79/1.18  #Demod        : 9
% 1.79/1.18  #Tautology    : 1
% 1.79/1.18  #SimpNegUnit  : 2
% 1.79/1.18  #BackRed      : 0
% 1.79/1.18  
% 1.79/1.18  #Partial instantiations: 0
% 1.79/1.18  #Strategies tried      : 1
% 1.79/1.18  
% 1.79/1.18  Timing (in seconds)
% 1.79/1.18  ----------------------
% 1.79/1.18  Preprocessing        : 0.26
% 1.79/1.18  Parsing              : 0.15
% 1.79/1.18  CNF conversion       : 0.02
% 1.79/1.18  Main loop            : 0.11
% 1.79/1.18  Inferencing          : 0.05
% 1.79/1.18  Reduction            : 0.03
% 1.79/1.18  Demodulation         : 0.02
% 1.79/1.18  BG Simplification    : 0.01
% 1.79/1.18  Subsumption          : 0.02
% 1.79/1.18  Abstraction          : 0.00
% 1.79/1.18  MUC search           : 0.00
% 1.79/1.18  Cooper               : 0.00
% 1.79/1.18  Total                : 0.41
% 1.79/1.18  Index Insertion      : 0.00
% 1.79/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
