%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 106 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :   98 ( 195 expanded)
%              Number of equality atoms :    6 (   8 expanded)
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

tff(f_78,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_29,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_29])).

tff(c_122,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_60,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k2_relat_1(B_37),A_38)
      | ~ v5_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_31] :
      ( r1_tarski(A_31,'#skF_4')
      | ~ r1_tarski(A_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_36])).

tff(c_67,plain,(
    ! [B_37] :
      ( r1_tarski(k2_relat_1(B_37),'#skF_4')
      | ~ v5_relat_1(B_37,'#skF_3')
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_60,c_44])).

tff(c_69,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_79,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_76])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_10])).

tff(c_97,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_93])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    ! [A_31] :
      ( r1_tarski(A_31,'#skF_2')
      | ~ r1_tarski(A_31,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_159,plain,(
    ! [D_52,B_53,C_54,A_55] :
      ( m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(B_53,C_54)))
      | ~ r1_tarski(k1_relat_1(D_52),B_53)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_55,C_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_165,plain,(
    ! [B_56] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_56,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_56) ) ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_183,plain,(
    ! [B_57] :
      ( v4_relat_1('#skF_5',B_57)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_57) ) ),
    inference(resolution,[status(thm)],[c_165,c_16])).

tff(c_190,plain,
    ( v4_relat_1('#skF_5','#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_183])).

tff(c_195,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_190])).

tff(c_198,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_195,c_8])).

tff(c_201,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_198])).

tff(c_205,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_10])).

tff(c_209,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_205])).

tff(c_223,plain,(
    ! [D_58,C_59,B_60,A_61] :
      ( m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(C_59,B_60)))
      | ~ r1_tarski(k2_relat_1(D_58),B_60)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(C_59,A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_248,plain,(
    ! [B_65] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_65)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_65) ) ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_18,plain,(
    ! [D_19,B_17,C_18,A_16] :
      ( m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(B_17,C_18)))
      | ~ r1_tarski(k1_relat_1(D_19),B_17)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_16,C_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_333,plain,(
    ! [B_74,B_75] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_74,B_75)))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_74)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_75) ) ),
    inference(resolution,[status(thm)],[c_248,c_18])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_349,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_333,c_22])).

tff(c_358,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_349])).

tff(c_361,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_358])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_126,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.29  
% 2.39/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.29  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.39/1.29  
% 2.39/1.29  %Foreground sorts:
% 2.39/1.29  
% 2.39/1.29  
% 2.39/1.29  %Background operators:
% 2.39/1.29  
% 2.39/1.29  
% 2.39/1.29  %Foreground operators:
% 2.39/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.39/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.39/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.39/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.29  
% 2.39/1.30  tff(f_78, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 2.39/1.30  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.39/1.30  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.39/1.30  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.39/1.30  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.39/1.30  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.39/1.30  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.39/1.30  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.39/1.30  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 2.39/1.30  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.30  tff(c_29, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.30  tff(c_33, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_29])).
% 2.39/1.30  tff(c_122, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.30  tff(c_126, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_122])).
% 2.39/1.30  tff(c_60, plain, (![B_37, A_38]: (r1_tarski(k2_relat_1(B_37), A_38) | ~v5_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.39/1.30  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.30  tff(c_36, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.30  tff(c_44, plain, (![A_31]: (r1_tarski(A_31, '#skF_4') | ~r1_tarski(A_31, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_36])).
% 2.39/1.30  tff(c_67, plain, (![B_37]: (r1_tarski(k2_relat_1(B_37), '#skF_4') | ~v5_relat_1(B_37, '#skF_3') | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_60, c_44])).
% 2.39/1.30  tff(c_69, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.30  tff(c_73, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_69])).
% 2.39/1.30  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.30  tff(c_76, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_73, c_8])).
% 2.39/1.30  tff(c_79, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_76])).
% 2.39/1.30  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.30  tff(c_93, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_79, c_10])).
% 2.39/1.30  tff(c_97, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_93])).
% 2.39/1.30  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.30  tff(c_45, plain, (![A_31]: (r1_tarski(A_31, '#skF_2') | ~r1_tarski(A_31, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_36])).
% 2.39/1.30  tff(c_159, plain, (![D_52, B_53, C_54, A_55]: (m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(B_53, C_54))) | ~r1_tarski(k1_relat_1(D_52), B_53) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_55, C_54))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.39/1.30  tff(c_165, plain, (![B_56]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_56, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_56))), inference(resolution, [status(thm)], [c_28, c_159])).
% 2.39/1.30  tff(c_16, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.30  tff(c_183, plain, (![B_57]: (v4_relat_1('#skF_5', B_57) | ~r1_tarski(k1_relat_1('#skF_5'), B_57))), inference(resolution, [status(thm)], [c_165, c_16])).
% 2.39/1.30  tff(c_190, plain, (v4_relat_1('#skF_5', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_45, c_183])).
% 2.39/1.30  tff(c_195, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_190])).
% 2.39/1.30  tff(c_198, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_195, c_8])).
% 2.39/1.30  tff(c_201, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_198])).
% 2.39/1.30  tff(c_205, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_201, c_10])).
% 2.39/1.30  tff(c_209, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_205])).
% 2.39/1.30  tff(c_223, plain, (![D_58, C_59, B_60, A_61]: (m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(C_59, B_60))) | ~r1_tarski(k2_relat_1(D_58), B_60) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(C_59, A_61))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.39/1.30  tff(c_248, plain, (![B_65]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_65))) | ~r1_tarski(k2_relat_1('#skF_5'), B_65))), inference(resolution, [status(thm)], [c_28, c_223])).
% 2.39/1.30  tff(c_18, plain, (![D_19, B_17, C_18, A_16]: (m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(B_17, C_18))) | ~r1_tarski(k1_relat_1(D_19), B_17) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_16, C_18))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.39/1.30  tff(c_333, plain, (![B_74, B_75]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_74, B_75))) | ~r1_tarski(k1_relat_1('#skF_5'), B_74) | ~r1_tarski(k2_relat_1('#skF_5'), B_75))), inference(resolution, [status(thm)], [c_248, c_18])).
% 2.39/1.30  tff(c_22, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.30  tff(c_349, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_333, c_22])).
% 2.39/1.30  tff(c_358, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_349])).
% 2.39/1.30  tff(c_361, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_67, c_358])).
% 2.39/1.30  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_126, c_361])).
% 2.39/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.30  
% 2.39/1.30  Inference rules
% 2.39/1.30  ----------------------
% 2.39/1.30  #Ref     : 0
% 2.39/1.30  #Sup     : 75
% 2.39/1.30  #Fact    : 0
% 2.39/1.30  #Define  : 0
% 2.39/1.30  #Split   : 3
% 2.39/1.30  #Chain   : 0
% 2.39/1.30  #Close   : 0
% 2.39/1.30  
% 2.39/1.30  Ordering : KBO
% 2.39/1.30  
% 2.39/1.30  Simplification rules
% 2.39/1.30  ----------------------
% 2.39/1.30  #Subsume      : 11
% 2.39/1.30  #Demod        : 25
% 2.39/1.30  #Tautology    : 16
% 2.39/1.30  #SimpNegUnit  : 0
% 2.39/1.30  #BackRed      : 0
% 2.39/1.30  
% 2.39/1.31  #Partial instantiations: 0
% 2.39/1.31  #Strategies tried      : 1
% 2.39/1.31  
% 2.39/1.31  Timing (in seconds)
% 2.39/1.31  ----------------------
% 2.39/1.31  Preprocessing        : 0.28
% 2.39/1.31  Parsing              : 0.16
% 2.39/1.31  CNF conversion       : 0.02
% 2.39/1.31  Main loop            : 0.25
% 2.39/1.31  Inferencing          : 0.10
% 2.39/1.31  Reduction            : 0.06
% 2.39/1.31  Demodulation         : 0.04
% 2.39/1.31  BG Simplification    : 0.01
% 2.39/1.31  Subsumption          : 0.06
% 2.39/1.31  Abstraction          : 0.01
% 2.39/1.31  MUC search           : 0.00
% 2.39/1.31  Cooper               : 0.00
% 2.39/1.31  Total                : 0.56
% 2.39/1.31  Index Insertion      : 0.00
% 2.39/1.31  Index Deletion       : 0.00
% 2.39/1.31  Index Matching       : 0.00
% 2.39/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
