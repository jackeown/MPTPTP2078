%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  97 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_76,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_86,plain,(
    ! [B_42,A_43] :
      ( k7_relat_1(B_42,A_43) = B_42
      | ~ v4_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_86])).

tff(c_92,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_89])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_8])).

tff(c_100,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_96])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_27,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_41,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_xboole_0(A_29,C_30)
      | ~ r1_xboole_0(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_29] :
      ( r1_xboole_0(A_29,'#skF_2')
      | ~ r1_tarski(A_29,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_151,plain,(
    ! [B_56,A_57] :
      ( k7_relat_1(B_56,A_57) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_56),A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    ! [B_61] :
      ( k7_relat_1(B_61,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_61)
      | ~ r1_tarski(k1_relat_1(B_61),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_151])).

tff(c_201,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_198])).

tff(c_208,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_201])).

tff(c_210,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k5_relset_1(A_62,B_63,C_64,D_65) = k7_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_213,plain,(
    ! [D_65] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_65) = k7_relat_1('#skF_4',D_65) ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_22,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_239,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_22])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:51:36 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.23  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.23  
% 2.15/1.23  %Foreground sorts:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Background operators:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Foreground operators:
% 2.15/1.23  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.15/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.23  
% 2.21/1.24  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.21/1.24  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.24  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.21/1.24  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.21/1.24  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.21/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.21/1.24  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.21/1.24  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.21/1.24  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.21/1.24  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.24  tff(c_36, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.24  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_36])).
% 2.21/1.24  tff(c_76, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.24  tff(c_80, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_76])).
% 2.21/1.24  tff(c_86, plain, (![B_42, A_43]: (k7_relat_1(B_42, A_43)=B_42 | ~v4_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.24  tff(c_89, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_86])).
% 2.21/1.24  tff(c_92, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_89])).
% 2.21/1.24  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.24  tff(c_96, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_92, c_8])).
% 2.21/1.24  tff(c_100, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_96])).
% 2.21/1.24  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.24  tff(c_27, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.24  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_27])).
% 2.21/1.24  tff(c_41, plain, (![A_29, C_30, B_31]: (r1_xboole_0(A_29, C_30) | ~r1_xboole_0(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.24  tff(c_46, plain, (![A_29]: (r1_xboole_0(A_29, '#skF_2') | ~r1_tarski(A_29, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.21/1.24  tff(c_151, plain, (![B_56, A_57]: (k7_relat_1(B_56, A_57)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_56), A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.24  tff(c_198, plain, (![B_61]: (k7_relat_1(B_61, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_61) | ~r1_tarski(k1_relat_1(B_61), '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_151])).
% 2.21/1.24  tff(c_201, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_198])).
% 2.21/1.24  tff(c_208, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_201])).
% 2.21/1.24  tff(c_210, plain, (![A_62, B_63, C_64, D_65]: (k5_relset_1(A_62, B_63, C_64, D_65)=k7_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.24  tff(c_213, plain, (![D_65]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_65)=k7_relat_1('#skF_4', D_65))), inference(resolution, [status(thm)], [c_26, c_210])).
% 2.21/1.24  tff(c_22, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.24  tff(c_239, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_213, c_22])).
% 2.21/1.24  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_239])).
% 2.21/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  Inference rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Ref     : 0
% 2.21/1.24  #Sup     : 52
% 2.21/1.24  #Fact    : 0
% 2.21/1.24  #Define  : 0
% 2.21/1.24  #Split   : 3
% 2.21/1.24  #Chain   : 0
% 2.21/1.24  #Close   : 0
% 2.21/1.24  
% 2.21/1.24  Ordering : KBO
% 2.21/1.24  
% 2.21/1.24  Simplification rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Subsume      : 6
% 2.21/1.24  #Demod        : 9
% 2.21/1.24  #Tautology    : 6
% 2.21/1.24  #SimpNegUnit  : 0
% 2.21/1.24  #BackRed      : 1
% 2.21/1.24  
% 2.21/1.24  #Partial instantiations: 0
% 2.21/1.24  #Strategies tried      : 1
% 2.21/1.24  
% 2.21/1.24  Timing (in seconds)
% 2.21/1.24  ----------------------
% 2.21/1.25  Preprocessing        : 0.29
% 2.21/1.25  Parsing              : 0.16
% 2.21/1.25  CNF conversion       : 0.02
% 2.21/1.25  Main loop            : 0.20
% 2.21/1.25  Inferencing          : 0.08
% 2.21/1.25  Reduction            : 0.05
% 2.21/1.25  Demodulation         : 0.03
% 2.21/1.25  BG Simplification    : 0.01
% 2.21/1.25  Subsumption          : 0.05
% 2.21/1.25  Abstraction          : 0.01
% 2.21/1.25  MUC search           : 0.00
% 2.21/1.25  Cooper               : 0.00
% 2.21/1.25  Total                : 0.52
% 2.21/1.25  Index Insertion      : 0.00
% 2.21/1.25  Index Deletion       : 0.00
% 2.21/1.25  Index Matching       : 0.00
% 2.21/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
