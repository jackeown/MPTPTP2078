%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   56 (  92 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 166 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_27,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_31,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_71,plain,(
    ! [C_35,B_36,A_37] :
      ( v5_relat_1(C_35,B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_57,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(k2_relat_1(B_30),A_31)
      | ~ v5_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(A_24,C_25)
      | ~ r1_tarski(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_4')
      | ~ r1_tarski(A_24,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_64,plain,(
    ! [B_30] :
      ( r1_tarski(k2_relat_1(B_30),'#skF_4')
      | ~ v5_relat_1(B_30,'#skF_3')
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_57,c_41])).

tff(c_66,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_66])).

tff(c_76,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ v4_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_82,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_79])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_90,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_86])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_2')
      | ~ r1_tarski(A_24,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_157,plain,(
    ! [C_47,A_48,B_49] :
      ( m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ r1_tarski(k2_relat_1(C_47),B_49)
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_169,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_20])).

tff(c_175,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_169])).

tff(c_178,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_181,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_181])).

tff(c_186,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_190,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_186])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_75,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.20  
% 1.95/1.20  %Foreground sorts:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Background operators:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Foreground operators:
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.95/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.20  
% 1.95/1.21  tff(f_74, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 1.95/1.21  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.95/1.21  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.95/1.21  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.95/1.21  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.95/1.21  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.95/1.21  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.95/1.21  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 1.95/1.21  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.21  tff(c_27, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.21  tff(c_31, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_27])).
% 1.95/1.21  tff(c_71, plain, (![C_35, B_36, A_37]: (v5_relat_1(C_35, B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.21  tff(c_75, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_71])).
% 1.95/1.21  tff(c_57, plain, (![B_30, A_31]: (r1_tarski(k2_relat_1(B_30), A_31) | ~v5_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.21  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.21  tff(c_33, plain, (![A_24, C_25, B_26]: (r1_tarski(A_24, C_25) | ~r1_tarski(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.21  tff(c_41, plain, (![A_24]: (r1_tarski(A_24, '#skF_4') | ~r1_tarski(A_24, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_33])).
% 1.95/1.21  tff(c_64, plain, (![B_30]: (r1_tarski(k2_relat_1(B_30), '#skF_4') | ~v5_relat_1(B_30, '#skF_3') | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_57, c_41])).
% 1.95/1.21  tff(c_66, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.21  tff(c_70, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_66])).
% 1.95/1.21  tff(c_76, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~v4_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.21  tff(c_79, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_76])).
% 1.95/1.21  tff(c_82, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_79])).
% 1.95/1.21  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.21  tff(c_86, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 1.95/1.21  tff(c_90, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_86])).
% 1.95/1.21  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.21  tff(c_42, plain, (![A_24]: (r1_tarski(A_24, '#skF_2') | ~r1_tarski(A_24, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_33])).
% 1.95/1.21  tff(c_157, plain, (![C_47, A_48, B_49]: (m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~r1_tarski(k2_relat_1(C_47), B_49) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.21  tff(c_20, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.21  tff(c_169, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_157, c_20])).
% 1.95/1.21  tff(c_175, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_169])).
% 1.95/1.21  tff(c_178, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_175])).
% 1.95/1.21  tff(c_181, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_178])).
% 1.95/1.21  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_181])).
% 1.95/1.21  tff(c_186, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_175])).
% 1.95/1.21  tff(c_190, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_186])).
% 1.95/1.21  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_75, c_190])).
% 1.95/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  Inference rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Ref     : 0
% 1.95/1.21  #Sup     : 38
% 1.95/1.21  #Fact    : 0
% 1.95/1.21  #Define  : 0
% 1.95/1.21  #Split   : 3
% 1.95/1.21  #Chain   : 0
% 1.95/1.21  #Close   : 0
% 1.95/1.21  
% 1.95/1.21  Ordering : KBO
% 1.95/1.21  
% 1.95/1.21  Simplification rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Subsume      : 2
% 1.95/1.21  #Demod        : 8
% 1.95/1.21  #Tautology    : 5
% 1.95/1.21  #SimpNegUnit  : 0
% 1.95/1.21  #BackRed      : 0
% 1.95/1.21  
% 1.95/1.21  #Partial instantiations: 0
% 1.95/1.21  #Strategies tried      : 1
% 1.95/1.21  
% 1.95/1.21  Timing (in seconds)
% 1.95/1.21  ----------------------
% 1.95/1.21  Preprocessing        : 0.27
% 1.95/1.21  Parsing              : 0.15
% 1.95/1.21  CNF conversion       : 0.02
% 1.95/1.21  Main loop            : 0.18
% 1.95/1.21  Inferencing          : 0.07
% 1.95/1.21  Reduction            : 0.05
% 1.95/1.21  Demodulation         : 0.03
% 1.95/1.21  BG Simplification    : 0.01
% 1.95/1.21  Subsumption          : 0.04
% 1.95/1.21  Abstraction          : 0.01
% 1.95/1.21  MUC search           : 0.00
% 1.95/1.21  Cooper               : 0.00
% 1.95/1.21  Total                : 0.48
% 1.95/1.21  Index Insertion      : 0.00
% 1.95/1.21  Index Deletion       : 0.00
% 1.95/1.21  Index Matching       : 0.00
% 1.95/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
