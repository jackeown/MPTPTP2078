%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 114 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 227 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_29])).

tff(c_65,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_29] :
      ( r1_tarski(A_29,'#skF_2')
      | ~ r1_tarski(A_29,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_205,plain,(
    ! [D_60,B_61,C_62,A_63] :
      ( m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ r1_tarski(k1_relat_1(D_60),B_61)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_63,C_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_212,plain,(
    ! [B_64] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_64,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_64) ) ),
    inference(resolution,[status(thm)],[c_28,c_205])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_233,plain,(
    ! [B_65] :
      ( v4_relat_1('#skF_5',B_65)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_65) ) ),
    inference(resolution,[status(thm)],[c_212,c_16])).

tff(c_252,plain,
    ( v4_relat_1('#skF_5','#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_233])).

tff(c_254,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_257,plain,
    ( ~ v4_relat_1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_69,c_257])).

tff(c_262,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_89,plain,(
    ! [C_41,B_42,A_43] :
      ( v5_relat_1(C_41,B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_4')
      | ~ r1_tarski(A_32,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_55,plain,(
    ! [B_7] :
      ( r1_tarski(k2_relat_1(B_7),'#skF_4')
      | ~ v5_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_50])).

tff(c_131,plain,(
    ! [D_51,C_52,B_53,A_54] :
      ( m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(C_52,B_53)))
      | ~ r1_tarski(k2_relat_1(D_51),B_53)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(C_52,A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_134,plain,(
    ! [B_53] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_53)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_53) ) ),
    inference(resolution,[status(thm)],[c_28,c_131])).

tff(c_308,plain,(
    ! [B_70,B_71] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_70,B_71)))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_70)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_71) ) ),
    inference(resolution,[status(thm)],[c_134,c_205])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_331,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_308,c_22])).

tff(c_332,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_335,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_332])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_93,c_335])).

tff(c_343,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_347,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_262,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.15/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.26  
% 2.15/1.28  tff(f_74, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 2.15/1.28  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.15/1.28  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.15/1.28  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.15/1.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.15/1.28  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.15/1.28  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.15/1.28  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 2.15/1.28  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_29, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.28  tff(c_33, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_29])).
% 2.15/1.28  tff(c_65, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.28  tff(c_69, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_65])).
% 2.15/1.28  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.28  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_40, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.28  tff(c_49, plain, (![A_29]: (r1_tarski(A_29, '#skF_2') | ~r1_tarski(A_29, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_40])).
% 2.15/1.28  tff(c_205, plain, (![D_60, B_61, C_62, A_63]: (m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~r1_tarski(k1_relat_1(D_60), B_61) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_63, C_62))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.28  tff(c_212, plain, (![B_64]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_64, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_64))), inference(resolution, [status(thm)], [c_28, c_205])).
% 2.15/1.28  tff(c_16, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.28  tff(c_233, plain, (![B_65]: (v4_relat_1('#skF_5', B_65) | ~r1_tarski(k1_relat_1('#skF_5'), B_65))), inference(resolution, [status(thm)], [c_212, c_16])).
% 2.15/1.28  tff(c_252, plain, (v4_relat_1('#skF_5', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_49, c_233])).
% 2.15/1.28  tff(c_254, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_252])).
% 2.15/1.28  tff(c_257, plain, (~v4_relat_1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_254])).
% 2.15/1.28  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_69, c_257])).
% 2.15/1.28  tff(c_262, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_252])).
% 2.15/1.28  tff(c_89, plain, (![C_41, B_42, A_43]: (v5_relat_1(C_41, B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.28  tff(c_93, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_89])).
% 2.15/1.28  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.28  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_50, plain, (![A_32]: (r1_tarski(A_32, '#skF_4') | ~r1_tarski(A_32, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.15/1.28  tff(c_55, plain, (![B_7]: (r1_tarski(k2_relat_1(B_7), '#skF_4') | ~v5_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_50])).
% 2.15/1.28  tff(c_131, plain, (![D_51, C_52, B_53, A_54]: (m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(C_52, B_53))) | ~r1_tarski(k2_relat_1(D_51), B_53) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(C_52, A_54))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.28  tff(c_134, plain, (![B_53]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_53))) | ~r1_tarski(k2_relat_1('#skF_5'), B_53))), inference(resolution, [status(thm)], [c_28, c_131])).
% 2.15/1.28  tff(c_308, plain, (![B_70, B_71]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_70, B_71))) | ~r1_tarski(k1_relat_1('#skF_5'), B_70) | ~r1_tarski(k2_relat_1('#skF_5'), B_71))), inference(resolution, [status(thm)], [c_134, c_205])).
% 2.15/1.28  tff(c_22, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_331, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_308, c_22])).
% 2.15/1.28  tff(c_332, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_331])).
% 2.15/1.28  tff(c_335, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_55, c_332])).
% 2.15/1.28  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_93, c_335])).
% 2.15/1.28  tff(c_343, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_331])).
% 2.15/1.28  tff(c_347, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_343])).
% 2.15/1.28  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_262, c_347])).
% 2.15/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  Inference rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Ref     : 0
% 2.15/1.28  #Sup     : 67
% 2.15/1.28  #Fact    : 0
% 2.15/1.28  #Define  : 0
% 2.15/1.28  #Split   : 6
% 2.15/1.28  #Chain   : 0
% 2.15/1.28  #Close   : 0
% 2.15/1.28  
% 2.15/1.28  Ordering : KBO
% 2.15/1.28  
% 2.15/1.28  Simplification rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Subsume      : 7
% 2.15/1.28  #Demod        : 25
% 2.15/1.28  #Tautology    : 14
% 2.15/1.28  #SimpNegUnit  : 0
% 2.15/1.28  #BackRed      : 0
% 2.15/1.28  
% 2.15/1.28  #Partial instantiations: 0
% 2.15/1.28  #Strategies tried      : 1
% 2.15/1.28  
% 2.15/1.28  Timing (in seconds)
% 2.15/1.28  ----------------------
% 2.15/1.28  Preprocessing        : 0.27
% 2.15/1.28  Parsing              : 0.15
% 2.15/1.28  CNF conversion       : 0.02
% 2.15/1.28  Main loop            : 0.24
% 2.15/1.28  Inferencing          : 0.10
% 2.15/1.28  Reduction            : 0.06
% 2.15/1.28  Demodulation         : 0.04
% 2.15/1.28  BG Simplification    : 0.01
% 2.15/1.28  Subsumption          : 0.05
% 2.15/1.28  Abstraction          : 0.01
% 2.15/1.28  MUC search           : 0.00
% 2.15/1.28  Cooper               : 0.00
% 2.15/1.28  Total                : 0.54
% 2.15/1.28  Index Insertion      : 0.00
% 2.15/1.28  Index Deletion       : 0.00
% 2.15/1.28  Index Matching       : 0.00
% 2.15/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
