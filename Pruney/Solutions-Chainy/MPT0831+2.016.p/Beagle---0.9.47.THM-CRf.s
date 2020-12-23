%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  83 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_49,plain,(
    ! [A_32,B_33,D_34] :
      ( r2_relset_1(A_32,B_33,D_34,D_34)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_23,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_23])).

tff(c_34,plain,(
    ! [C_29,A_30,B_31] :
      ( v4_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_34])).

tff(c_53,plain,(
    ! [C_35,B_36,A_37] :
      ( v4_relat_1(C_35,B_36)
      | ~ v4_relat_1(C_35,A_37)
      | ~ v1_relat_1(C_35)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [B_36] :
      ( v4_relat_1('#skF_4',B_36)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_36) ) ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_59,plain,(
    ! [B_38] :
      ( v4_relat_1('#skF_4',B_38)
      | ~ r1_tarski('#skF_2',B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [B_38] :
      ( k7_relat_1('#skF_4',B_38) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_38) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_75,plain,(
    ! [B_43] :
      ( k7_relat_1('#skF_4',B_43) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_64])).

tff(c_79,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_71,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k5_relset_1(A_39,B_40,C_41,D_42) = k7_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    ! [D_42] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_42) = k7_relat_1('#skF_4',D_42) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_79,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.25  
% 1.93/1.25  %Foreground sorts:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Background operators:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Foreground operators:
% 1.93/1.25  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.25  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.93/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.25  
% 1.93/1.26  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 1.93/1.26  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.93/1.26  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.26  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.93/1.26  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 1.93/1.26  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.93/1.26  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.93/1.26  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.26  tff(c_49, plain, (![A_32, B_33, D_34]: (r2_relset_1(A_32, B_33, D_34, D_34) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.26  tff(c_52, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_49])).
% 1.93/1.26  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.26  tff(c_23, plain, (![C_21, A_22, B_23]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.26  tff(c_27, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_23])).
% 1.93/1.26  tff(c_34, plain, (![C_29, A_30, B_31]: (v4_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.26  tff(c_38, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_34])).
% 1.93/1.26  tff(c_53, plain, (![C_35, B_36, A_37]: (v4_relat_1(C_35, B_36) | ~v4_relat_1(C_35, A_37) | ~v1_relat_1(C_35) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.26  tff(c_55, plain, (![B_36]: (v4_relat_1('#skF_4', B_36) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_36))), inference(resolution, [status(thm)], [c_38, c_53])).
% 1.93/1.26  tff(c_59, plain, (![B_38]: (v4_relat_1('#skF_4', B_38) | ~r1_tarski('#skF_2', B_38))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_55])).
% 1.93/1.26  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.26  tff(c_64, plain, (![B_38]: (k7_relat_1('#skF_4', B_38)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_38))), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.93/1.26  tff(c_75, plain, (![B_43]: (k7_relat_1('#skF_4', B_43)='#skF_4' | ~r1_tarski('#skF_2', B_43))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_64])).
% 1.93/1.26  tff(c_79, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_75])).
% 1.93/1.26  tff(c_71, plain, (![A_39, B_40, C_41, D_42]: (k5_relset_1(A_39, B_40, C_41, D_42)=k7_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.26  tff(c_74, plain, (![D_42]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_42)=k7_relat_1('#skF_4', D_42))), inference(resolution, [status(thm)], [c_22, c_71])).
% 1.93/1.26  tff(c_18, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.26  tff(c_84, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 1.93/1.26  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_79, c_84])).
% 1.93/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  Inference rules
% 1.93/1.26  ----------------------
% 1.93/1.26  #Ref     : 0
% 1.93/1.26  #Sup     : 14
% 1.93/1.26  #Fact    : 0
% 1.93/1.26  #Define  : 0
% 1.93/1.26  #Split   : 0
% 1.93/1.26  #Chain   : 0
% 1.93/1.26  #Close   : 0
% 1.93/1.26  
% 1.93/1.26  Ordering : KBO
% 1.93/1.26  
% 1.93/1.26  Simplification rules
% 1.93/1.26  ----------------------
% 1.93/1.26  #Subsume      : 0
% 1.93/1.26  #Demod        : 7
% 1.93/1.26  #Tautology    : 4
% 1.93/1.26  #SimpNegUnit  : 0
% 1.93/1.26  #BackRed      : 1
% 1.93/1.26  
% 1.93/1.26  #Partial instantiations: 0
% 1.93/1.26  #Strategies tried      : 1
% 1.93/1.26  
% 1.93/1.26  Timing (in seconds)
% 1.93/1.26  ----------------------
% 1.93/1.26  Preprocessing        : 0.32
% 1.93/1.26  Parsing              : 0.17
% 1.93/1.26  CNF conversion       : 0.02
% 1.93/1.26  Main loop            : 0.11
% 1.93/1.26  Inferencing          : 0.04
% 1.93/1.26  Reduction            : 0.03
% 1.93/1.26  Demodulation         : 0.03
% 1.93/1.26  BG Simplification    : 0.01
% 1.93/1.27  Subsumption          : 0.02
% 1.93/1.27  Abstraction          : 0.01
% 1.93/1.27  MUC search           : 0.00
% 1.93/1.27  Cooper               : 0.00
% 1.93/1.27  Total                : 0.46
% 1.93/1.27  Index Insertion      : 0.00
% 1.93/1.27  Index Deletion       : 0.00
% 1.93/1.27  Index Matching       : 0.00
% 1.93/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
