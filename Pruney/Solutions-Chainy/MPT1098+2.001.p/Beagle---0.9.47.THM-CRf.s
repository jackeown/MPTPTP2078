%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 178 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_52,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_293,plain,(
    ! [A_97,B_98,C_99] :
      ( v1_finset_1('#skF_1'(A_97,B_98,C_99))
      | ~ r1_tarski(A_97,k2_zfmisc_1(B_98,C_99))
      | ~ v1_finset_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_308,plain,
    ( v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_293])).

tff(c_318,plain,(
    v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_308])).

tff(c_44,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski('#skF_1'(A_27,B_28,C_29),B_28)
      | ~ r1_tarski(A_27,k2_zfmisc_1(B_28,C_29))
      | ~ v1_finset_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_614,plain,(
    ! [A_178,B_179,C_180] :
      ( r1_tarski(A_178,k2_zfmisc_1('#skF_1'(A_178,B_179,C_180),'#skF_2'(A_178,B_179,C_180)))
      | ~ r1_tarski(A_178,k2_zfmisc_1(B_179,C_180))
      | ~ v1_finset_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125,plain,(
    ! [A_3,A_57,B_58] :
      ( v4_relat_1(A_3,A_57)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_10,c_120])).

tff(c_648,plain,(
    ! [A_178,B_179,C_180] :
      ( v4_relat_1(A_178,'#skF_1'(A_178,B_179,C_180))
      | ~ r1_tarski(A_178,k2_zfmisc_1(B_179,C_180))
      | ~ v1_finset_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_614,c_125])).

tff(c_98,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    ! [A_53,A_54,B_55] :
      ( v1_relat_1(A_53)
      | ~ r1_tarski(A_53,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_209,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_215,plain,(
    ! [A_83,B_84,A_85] :
      ( v5_relat_1(A_83,B_84)
      | ~ r1_tarski(A_83,k2_zfmisc_1(A_85,B_84)) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_238,plain,(
    v5_relat_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_215])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_557,plain,(
    ! [C_165,A_166,B_167] :
      ( m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ r1_tarski(k2_relat_1(C_165),B_167)
      | ~ r1_tarski(k1_relat_1(C_165),A_166)
      | ~ v1_relat_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1051,plain,(
    ! [C_230,A_231,B_232] :
      ( r1_tarski(C_230,k2_zfmisc_1(A_231,B_232))
      | ~ r1_tarski(k2_relat_1(C_230),B_232)
      | ~ r1_tarski(k1_relat_1(C_230),A_231)
      | ~ v1_relat_1(C_230) ) ),
    inference(resolution,[status(thm)],[c_557,c_8])).

tff(c_1147,plain,(
    ! [B_273,A_274,A_275] :
      ( r1_tarski(B_273,k2_zfmisc_1(A_274,A_275))
      | ~ r1_tarski(k1_relat_1(B_273),A_274)
      | ~ v5_relat_1(B_273,A_275)
      | ~ v1_relat_1(B_273) ) ),
    inference(resolution,[status(thm)],[c_18,c_1051])).

tff(c_1297,plain,(
    ! [B_289,A_290,A_291] :
      ( r1_tarski(B_289,k2_zfmisc_1(A_290,A_291))
      | ~ v5_relat_1(B_289,A_291)
      | ~ v4_relat_1(B_289,A_290)
      | ~ v1_relat_1(B_289) ) ),
    inference(resolution,[status(thm)],[c_14,c_1147])).

tff(c_48,plain,(
    ! [D_33] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_33,'#skF_5'))
      | ~ r1_tarski(D_33,'#skF_4')
      | ~ v1_finset_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1338,plain,(
    ! [A_290] :
      ( ~ r1_tarski(A_290,'#skF_4')
      | ~ v1_finset_1(A_290)
      | ~ v5_relat_1('#skF_3','#skF_5')
      | ~ v4_relat_1('#skF_3',A_290)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1297,c_48])).

tff(c_1358,plain,(
    ! [A_292] :
      ( ~ r1_tarski(A_292,'#skF_4')
      | ~ v1_finset_1(A_292)
      | ~ v4_relat_1('#skF_3',A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_238,c_1338])).

tff(c_1362,plain,(
    ! [B_179,C_180] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_179,C_180),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_179,C_180))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_179,C_180))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_648,c_1358])).

tff(c_1495,plain,(
    ! [B_314,C_315] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_314,C_315),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_314,C_315))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_314,C_315)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1362])).

tff(c_1499,plain,(
    ! [C_29] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_29))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_29))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_1495])).

tff(c_1503,plain,(
    ! [C_316] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_316))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_316)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1499])).

tff(c_1514,plain,(
    ~ v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_1503])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.70  
% 3.85/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.70  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.85/1.70  
% 3.85/1.70  %Foreground sorts:
% 3.85/1.70  
% 3.85/1.70  
% 3.85/1.70  %Background operators:
% 3.85/1.70  
% 3.85/1.70  
% 3.85/1.70  %Foreground operators:
% 3.85/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.85/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.85/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.85/1.70  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 3.85/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.70  
% 3.85/1.71  tff(f_117, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 3.85/1.71  tff(f_103, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 3.85/1.71  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.71  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.71  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.85/1.71  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.85/1.71  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.85/1.71  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.85/1.71  tff(c_52, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.85/1.71  tff(c_50, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.85/1.71  tff(c_293, plain, (![A_97, B_98, C_99]: (v1_finset_1('#skF_1'(A_97, B_98, C_99)) | ~r1_tarski(A_97, k2_zfmisc_1(B_98, C_99)) | ~v1_finset_1(A_97))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.71  tff(c_308, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_293])).
% 3.85/1.71  tff(c_318, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_308])).
% 3.85/1.71  tff(c_44, plain, (![A_27, B_28, C_29]: (r1_tarski('#skF_1'(A_27, B_28, C_29), B_28) | ~r1_tarski(A_27, k2_zfmisc_1(B_28, C_29)) | ~v1_finset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.71  tff(c_614, plain, (![A_178, B_179, C_180]: (r1_tarski(A_178, k2_zfmisc_1('#skF_1'(A_178, B_179, C_180), '#skF_2'(A_178, B_179, C_180))) | ~r1_tarski(A_178, k2_zfmisc_1(B_179, C_180)) | ~v1_finset_1(A_178))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.71  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.71  tff(c_120, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.71  tff(c_125, plain, (![A_3, A_57, B_58]: (v4_relat_1(A_3, A_57) | ~r1_tarski(A_3, k2_zfmisc_1(A_57, B_58)))), inference(resolution, [status(thm)], [c_10, c_120])).
% 3.85/1.71  tff(c_648, plain, (![A_178, B_179, C_180]: (v4_relat_1(A_178, '#skF_1'(A_178, B_179, C_180)) | ~r1_tarski(A_178, k2_zfmisc_1(B_179, C_180)) | ~v1_finset_1(A_178))), inference(resolution, [status(thm)], [c_614, c_125])).
% 3.85/1.71  tff(c_98, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.85/1.71  tff(c_104, plain, (![A_53, A_54, B_55]: (v1_relat_1(A_53) | ~r1_tarski(A_53, k2_zfmisc_1(A_54, B_55)))), inference(resolution, [status(thm)], [c_10, c_98])).
% 3.85/1.71  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_104])).
% 3.85/1.71  tff(c_209, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.85/1.71  tff(c_215, plain, (![A_83, B_84, A_85]: (v5_relat_1(A_83, B_84) | ~r1_tarski(A_83, k2_zfmisc_1(A_85, B_84)))), inference(resolution, [status(thm)], [c_10, c_209])).
% 3.85/1.71  tff(c_238, plain, (v5_relat_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_215])).
% 3.85/1.71  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k1_relat_1(B_6), A_5) | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/1.71  tff(c_18, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.85/1.71  tff(c_557, plain, (![C_165, A_166, B_167]: (m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~r1_tarski(k2_relat_1(C_165), B_167) | ~r1_tarski(k1_relat_1(C_165), A_166) | ~v1_relat_1(C_165))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.85/1.71  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.71  tff(c_1051, plain, (![C_230, A_231, B_232]: (r1_tarski(C_230, k2_zfmisc_1(A_231, B_232)) | ~r1_tarski(k2_relat_1(C_230), B_232) | ~r1_tarski(k1_relat_1(C_230), A_231) | ~v1_relat_1(C_230))), inference(resolution, [status(thm)], [c_557, c_8])).
% 3.85/1.71  tff(c_1147, plain, (![B_273, A_274, A_275]: (r1_tarski(B_273, k2_zfmisc_1(A_274, A_275)) | ~r1_tarski(k1_relat_1(B_273), A_274) | ~v5_relat_1(B_273, A_275) | ~v1_relat_1(B_273))), inference(resolution, [status(thm)], [c_18, c_1051])).
% 3.85/1.71  tff(c_1297, plain, (![B_289, A_290, A_291]: (r1_tarski(B_289, k2_zfmisc_1(A_290, A_291)) | ~v5_relat_1(B_289, A_291) | ~v4_relat_1(B_289, A_290) | ~v1_relat_1(B_289))), inference(resolution, [status(thm)], [c_14, c_1147])).
% 3.85/1.71  tff(c_48, plain, (![D_33]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_33, '#skF_5')) | ~r1_tarski(D_33, '#skF_4') | ~v1_finset_1(D_33))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.85/1.71  tff(c_1338, plain, (![A_290]: (~r1_tarski(A_290, '#skF_4') | ~v1_finset_1(A_290) | ~v5_relat_1('#skF_3', '#skF_5') | ~v4_relat_1('#skF_3', A_290) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1297, c_48])).
% 3.85/1.71  tff(c_1358, plain, (![A_292]: (~r1_tarski(A_292, '#skF_4') | ~v1_finset_1(A_292) | ~v4_relat_1('#skF_3', A_292))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_238, c_1338])).
% 3.85/1.71  tff(c_1362, plain, (![B_179, C_180]: (~r1_tarski('#skF_1'('#skF_3', B_179, C_180), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_179, C_180)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_179, C_180)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_648, c_1358])).
% 3.85/1.71  tff(c_1495, plain, (![B_314, C_315]: (~r1_tarski('#skF_1'('#skF_3', B_314, C_315), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_314, C_315)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_314, C_315)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1362])).
% 3.85/1.71  tff(c_1499, plain, (![C_29]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_29)) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_29)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1495])).
% 3.85/1.71  tff(c_1503, plain, (![C_316]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_316)) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_316)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1499])).
% 3.85/1.71  tff(c_1514, plain, (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_1503])).
% 3.85/1.71  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_1514])).
% 3.85/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.71  
% 3.85/1.71  Inference rules
% 3.85/1.71  ----------------------
% 3.85/1.71  #Ref     : 0
% 3.85/1.71  #Sup     : 272
% 3.85/1.71  #Fact    : 0
% 3.85/1.71  #Define  : 0
% 3.85/1.71  #Split   : 3
% 3.85/1.71  #Chain   : 0
% 3.85/1.71  #Close   : 0
% 3.85/1.71  
% 3.85/1.71  Ordering : KBO
% 3.85/1.71  
% 3.85/1.71  Simplification rules
% 3.85/1.71  ----------------------
% 3.85/1.71  #Subsume      : 28
% 3.85/1.71  #Demod        : 116
% 3.85/1.71  #Tautology    : 33
% 3.85/1.71  #SimpNegUnit  : 0
% 3.85/1.71  #BackRed      : 0
% 3.85/1.71  
% 3.85/1.71  #Partial instantiations: 0
% 3.85/1.71  #Strategies tried      : 1
% 3.85/1.71  
% 3.85/1.71  Timing (in seconds)
% 3.85/1.71  ----------------------
% 3.85/1.72  Preprocessing        : 0.33
% 3.85/1.72  Parsing              : 0.18
% 3.85/1.72  CNF conversion       : 0.02
% 3.85/1.72  Main loop            : 0.54
% 3.85/1.72  Inferencing          : 0.21
% 3.85/1.72  Reduction            : 0.16
% 3.85/1.72  Demodulation         : 0.12
% 3.85/1.72  BG Simplification    : 0.02
% 3.85/1.72  Subsumption          : 0.11
% 3.85/1.72  Abstraction          : 0.02
% 3.85/1.72  MUC search           : 0.00
% 3.85/1.72  Cooper               : 0.00
% 3.85/1.72  Total                : 0.90
% 3.85/1.72  Index Insertion      : 0.00
% 3.85/1.72  Index Deletion       : 0.00
% 3.85/1.72  Index Matching       : 0.00
% 3.85/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
