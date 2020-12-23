%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   56 (  95 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 178 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_29,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_33,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_29])).

tff(c_46,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_56,plain,(
    ! [C_39,B_40,A_41] :
      ( v5_relat_1(C_39,B_40)
      | ~ v5_relat_1(C_39,A_41)
      | ~ v1_relat_1(C_39)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    ! [B_40] :
      ( v5_relat_1('#skF_5',B_40)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_40) ) ),
    inference(resolution,[status(thm)],[c_50,c_56])).

tff(c_61,plain,(
    ! [B_40] :
      ( v5_relat_1('#skF_5',B_40)
      | ~ r1_tarski('#skF_3',B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_58])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_51,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_55,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_62,plain,(
    ! [C_42,B_43,A_44] :
      ( v4_relat_1(C_42,B_43)
      | ~ v4_relat_1(C_42,A_44)
      | ~ v1_relat_1(C_42)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [B_43] :
      ( v4_relat_1('#skF_5',B_43)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_1',B_43) ) ),
    inference(resolution,[status(thm)],[c_55,c_62])).

tff(c_67,plain,(
    ! [B_43] :
      ( v4_relat_1('#skF_5',B_43)
      | ~ r1_tarski('#skF_1',B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_64])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [C_51,A_52,B_53] :
      ( m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ r1_tarski(k2_relat_1(C_51),B_53)
      | ~ r1_tarski(k1_relat_1(C_51),A_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_121,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_22])).

tff(c_127,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_121])).

tff(c_129,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_132,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_135,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_132])).

tff(c_138,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_138])).

tff(c_143,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_147,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_150,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_147])).

tff(c_153,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:58:15 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.45  
% 2.07/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.45  
% 2.07/1.45  %Foreground sorts:
% 2.07/1.45  
% 2.07/1.45  
% 2.07/1.45  %Background operators:
% 2.07/1.45  
% 2.07/1.45  
% 2.07/1.45  %Foreground operators:
% 2.07/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.07/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.07/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.45  
% 2.31/1.47  tff(f_82, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.31/1.47  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.31/1.47  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.31/1.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 2.31/1.47  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.31/1.47  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.31/1.47  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.31/1.47  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.31/1.47  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.47  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.47  tff(c_29, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.47  tff(c_33, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_29])).
% 2.31/1.47  tff(c_46, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.47  tff(c_50, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.31/1.47  tff(c_56, plain, (![C_39, B_40, A_41]: (v5_relat_1(C_39, B_40) | ~v5_relat_1(C_39, A_41) | ~v1_relat_1(C_39) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.47  tff(c_58, plain, (![B_40]: (v5_relat_1('#skF_5', B_40) | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_40))), inference(resolution, [status(thm)], [c_50, c_56])).
% 2.31/1.47  tff(c_61, plain, (![B_40]: (v5_relat_1('#skF_5', B_40) | ~r1_tarski('#skF_3', B_40))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_58])).
% 2.31/1.47  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.47  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.47  tff(c_51, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.47  tff(c_55, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.31/1.47  tff(c_62, plain, (![C_42, B_43, A_44]: (v4_relat_1(C_42, B_43) | ~v4_relat_1(C_42, A_44) | ~v1_relat_1(C_42) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.47  tff(c_64, plain, (![B_43]: (v4_relat_1('#skF_5', B_43) | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_1', B_43))), inference(resolution, [status(thm)], [c_55, c_62])).
% 2.31/1.47  tff(c_67, plain, (![B_43]: (v4_relat_1('#skF_5', B_43) | ~r1_tarski('#skF_1', B_43))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_64])).
% 2.31/1.47  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.47  tff(c_109, plain, (![C_51, A_52, B_53]: (m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~r1_tarski(k2_relat_1(C_51), B_53) | ~r1_tarski(k1_relat_1(C_51), A_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.31/1.47  tff(c_22, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.47  tff(c_121, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_109, c_22])).
% 2.31/1.47  tff(c_127, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_121])).
% 2.31/1.47  tff(c_129, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_127])).
% 2.31/1.47  tff(c_132, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4, c_129])).
% 2.31/1.47  tff(c_135, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_132])).
% 2.31/1.47  tff(c_138, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_135])).
% 2.31/1.47  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_138])).
% 2.31/1.47  tff(c_143, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_127])).
% 2.31/1.47  tff(c_147, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_143])).
% 2.31/1.47  tff(c_150, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_147])).
% 2.31/1.47  tff(c_153, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_61, c_150])).
% 2.31/1.47  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_153])).
% 2.31/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.47  
% 2.31/1.47  Inference rules
% 2.31/1.47  ----------------------
% 2.31/1.47  #Ref     : 0
% 2.31/1.47  #Sup     : 25
% 2.31/1.47  #Fact    : 0
% 2.31/1.47  #Define  : 0
% 2.31/1.47  #Split   : 5
% 2.31/1.47  #Chain   : 0
% 2.31/1.47  #Close   : 0
% 2.31/1.47  
% 2.31/1.47  Ordering : KBO
% 2.31/1.47  
% 2.31/1.47  Simplification rules
% 2.31/1.47  ----------------------
% 2.31/1.47  #Subsume      : 2
% 2.31/1.47  #Demod        : 9
% 2.31/1.47  #Tautology    : 3
% 2.31/1.47  #SimpNegUnit  : 0
% 2.31/1.47  #BackRed      : 0
% 2.31/1.47  
% 2.31/1.47  #Partial instantiations: 0
% 2.31/1.47  #Strategies tried      : 1
% 2.31/1.47  
% 2.31/1.47  Timing (in seconds)
% 2.31/1.47  ----------------------
% 2.31/1.47  Preprocessing        : 0.45
% 2.31/1.47  Parsing              : 0.26
% 2.31/1.47  CNF conversion       : 0.03
% 2.31/1.47  Main loop            : 0.21
% 2.31/1.47  Inferencing          : 0.08
% 2.31/1.47  Reduction            : 0.06
% 2.31/1.47  Demodulation         : 0.04
% 2.31/1.47  BG Simplification    : 0.02
% 2.31/1.47  Subsumption          : 0.05
% 2.31/1.47  Abstraction          : 0.01
% 2.31/1.47  MUC search           : 0.00
% 2.31/1.47  Cooper               : 0.00
% 2.31/1.47  Total                : 0.71
% 2.31/1.47  Index Insertion      : 0.00
% 2.31/1.47  Index Deletion       : 0.00
% 2.31/1.47  Index Matching       : 0.00
% 2.31/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
