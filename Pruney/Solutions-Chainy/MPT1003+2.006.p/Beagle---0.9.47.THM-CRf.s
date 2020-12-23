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
% DateTime   : Thu Dec  3 10:13:59 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 125 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 283 expanded)
%              Number of equality atoms :   24 ( 131 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_39,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [B_18,C_19,A_17,D_20] :
      ( k1_xboole_0 = B_18
      | r1_tarski(C_19,k8_relset_1(A_17,B_18,D_20,k7_relset_1(A_17,B_18,D_20,C_19)))
      | ~ r1_tarski(C_19,A_17)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(D_20,A_17,B_18)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( m1_subset_1(k8_relset_1(A_50,B_51,C_52,D_53),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r1_tarski(k8_relset_1(A_65,B_66,C_67,D_68),A_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(resolution,[status(thm)],[c_121,c_16])).

tff(c_183,plain,(
    ! [D_69] : r1_tarski(k8_relset_1('#skF_2','#skF_3','#skF_4',D_69),'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_226,plain,(
    ! [D_78] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',D_78) = '#skF_2'
      | ~ r1_tarski('#skF_2',k8_relset_1('#skF_2','#skF_3','#skF_4',D_78)) ) ),
    inference(resolution,[status(thm)],[c_183,c_10])).

tff(c_230,plain,
    ( k8_relset_1('#skF_2','#skF_3','#skF_4',k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_2')) = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_226])).

tff(c_236,plain,
    ( k8_relset_1('#skF_2','#skF_3','#skF_4',k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_2')) = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_14,c_230])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_28,c_236])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_239,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_246,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_239])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_8])).

tff(c_251,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_241])).

tff(c_252,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_32])).

tff(c_340,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( m1_subset_1(k8_relset_1(A_107,B_108,C_109,D_110),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_391,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( r1_tarski(k8_relset_1(A_122,B_123,C_124,D_125),A_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(resolution,[status(thm)],[c_340,c_16])).

tff(c_403,plain,(
    ! [D_126] : r1_tarski(k8_relset_1('#skF_3','#skF_3','#skF_4',D_126),'#skF_3') ),
    inference(resolution,[status(thm)],[c_252,c_391])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    ! [C_89,B_90,A_91] :
      ( ~ v1_xboole_0(C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_299,plain,(
    ! [B_95,A_96,A_97] :
      ( ~ v1_xboole_0(B_95)
      | ~ r2_hidden(A_96,A_97)
      | ~ r1_tarski(A_97,B_95) ) ),
    inference(resolution,[status(thm)],[c_18,c_287])).

tff(c_304,plain,(
    ! [B_98,A_99,B_100] :
      ( ~ v1_xboole_0(B_98)
      | ~ r1_tarski(A_99,B_98)
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_299])).

tff(c_311,plain,(
    ! [B_101,B_102] :
      ( ~ v1_xboole_0(B_101)
      | r1_tarski(B_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_14,c_304])).

tff(c_321,plain,(
    ! [B_102,B_101] :
      ( B_102 = B_101
      | ~ r1_tarski(B_102,B_101)
      | ~ v1_xboole_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_311,c_10])).

tff(c_408,plain,(
    ! [D_126] :
      ( k8_relset_1('#skF_3','#skF_3','#skF_4',D_126) = '#skF_3'
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_403,c_321])).

tff(c_418,plain,(
    ! [D_126] : k8_relset_1('#skF_3','#skF_3','#skF_4',D_126) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_408])).

tff(c_263,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_4',k7_relset_1('#skF_3','#skF_3','#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_246,c_246,c_246,c_28])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:46:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.31  
% 2.55/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.55/1.31  
% 2.55/1.31  %Foreground sorts:
% 2.55/1.31  
% 2.55/1.31  
% 2.55/1.31  %Background operators:
% 2.55/1.31  
% 2.55/1.31  
% 2.55/1.31  %Foreground operators:
% 2.55/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.31  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.31  
% 2.55/1.33  tff(f_82, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_2)).
% 2.55/1.33  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.33  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 2.55/1.33  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.55/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.55/1.33  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.33  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.55/1.33  tff(c_30, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.33  tff(c_39, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.55/1.33  tff(c_28, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.33  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.33  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.33  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.33  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.33  tff(c_26, plain, (![B_18, C_19, A_17, D_20]: (k1_xboole_0=B_18 | r1_tarski(C_19, k8_relset_1(A_17, B_18, D_20, k7_relset_1(A_17, B_18, D_20, C_19))) | ~r1_tarski(C_19, A_17) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(D_20, A_17, B_18) | ~v1_funct_1(D_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.33  tff(c_121, plain, (![A_50, B_51, C_52, D_53]: (m1_subset_1(k8_relset_1(A_50, B_51, C_52, D_53), k1_zfmisc_1(A_50)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.33  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.33  tff(c_171, plain, (![A_65, B_66, C_67, D_68]: (r1_tarski(k8_relset_1(A_65, B_66, C_67, D_68), A_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(resolution, [status(thm)], [c_121, c_16])).
% 2.55/1.33  tff(c_183, plain, (![D_69]: (r1_tarski(k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_69), '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_171])).
% 2.55/1.33  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.33  tff(c_226, plain, (![D_78]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_78)='#skF_2' | ~r1_tarski('#skF_2', k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_78)))), inference(resolution, [status(thm)], [c_183, c_10])).
% 2.55/1.33  tff(c_230, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'))='#skF_2' | k1_xboole_0='#skF_3' | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_226])).
% 2.55/1.33  tff(c_236, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'))='#skF_2' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_14, c_230])).
% 2.55/1.33  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_28, c_236])).
% 2.55/1.33  tff(c_240, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.55/1.33  tff(c_239, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.55/1.33  tff(c_246, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_239])).
% 2.55/1.33  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.33  tff(c_241, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_8])).
% 2.55/1.33  tff(c_251, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_241])).
% 2.55/1.33  tff(c_252, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_32])).
% 2.55/1.33  tff(c_340, plain, (![A_107, B_108, C_109, D_110]: (m1_subset_1(k8_relset_1(A_107, B_108, C_109, D_110), k1_zfmisc_1(A_107)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.33  tff(c_391, plain, (![A_122, B_123, C_124, D_125]: (r1_tarski(k8_relset_1(A_122, B_123, C_124, D_125), A_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(resolution, [status(thm)], [c_340, c_16])).
% 2.55/1.33  tff(c_403, plain, (![D_126]: (r1_tarski(k8_relset_1('#skF_3', '#skF_3', '#skF_4', D_126), '#skF_3'))), inference(resolution, [status(thm)], [c_252, c_391])).
% 2.55/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.33  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.33  tff(c_287, plain, (![C_89, B_90, A_91]: (~v1_xboole_0(C_89) | ~m1_subset_1(B_90, k1_zfmisc_1(C_89)) | ~r2_hidden(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.55/1.33  tff(c_299, plain, (![B_95, A_96, A_97]: (~v1_xboole_0(B_95) | ~r2_hidden(A_96, A_97) | ~r1_tarski(A_97, B_95))), inference(resolution, [status(thm)], [c_18, c_287])).
% 2.55/1.33  tff(c_304, plain, (![B_98, A_99, B_100]: (~v1_xboole_0(B_98) | ~r1_tarski(A_99, B_98) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_6, c_299])).
% 2.55/1.33  tff(c_311, plain, (![B_101, B_102]: (~v1_xboole_0(B_101) | r1_tarski(B_101, B_102))), inference(resolution, [status(thm)], [c_14, c_304])).
% 2.55/1.33  tff(c_321, plain, (![B_102, B_101]: (B_102=B_101 | ~r1_tarski(B_102, B_101) | ~v1_xboole_0(B_101))), inference(resolution, [status(thm)], [c_311, c_10])).
% 2.55/1.33  tff(c_408, plain, (![D_126]: (k8_relset_1('#skF_3', '#skF_3', '#skF_4', D_126)='#skF_3' | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_403, c_321])).
% 2.55/1.33  tff(c_418, plain, (![D_126]: (k8_relset_1('#skF_3', '#skF_3', '#skF_4', D_126)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_408])).
% 2.55/1.33  tff(c_263, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_4', k7_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_246, c_246, c_246, c_28])).
% 2.55/1.33  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_418, c_263])).
% 2.55/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  Inference rules
% 2.55/1.33  ----------------------
% 2.55/1.33  #Ref     : 0
% 2.55/1.33  #Sup     : 92
% 2.55/1.33  #Fact    : 0
% 2.55/1.33  #Define  : 0
% 2.55/1.33  #Split   : 6
% 2.55/1.33  #Chain   : 0
% 2.55/1.33  #Close   : 0
% 2.55/1.33  
% 2.55/1.33  Ordering : KBO
% 2.55/1.33  
% 2.55/1.33  Simplification rules
% 2.55/1.33  ----------------------
% 2.55/1.33  #Subsume      : 16
% 2.55/1.33  #Demod        : 29
% 2.55/1.33  #Tautology    : 20
% 2.55/1.33  #SimpNegUnit  : 1
% 2.55/1.33  #BackRed      : 7
% 2.55/1.33  
% 2.55/1.33  #Partial instantiations: 0
% 2.55/1.33  #Strategies tried      : 1
% 2.55/1.33  
% 2.55/1.33  Timing (in seconds)
% 2.55/1.33  ----------------------
% 2.55/1.33  Preprocessing        : 0.29
% 2.55/1.33  Parsing              : 0.16
% 2.55/1.33  CNF conversion       : 0.02
% 2.55/1.33  Main loop            : 0.27
% 2.55/1.33  Inferencing          : 0.10
% 2.55/1.33  Reduction            : 0.07
% 2.55/1.33  Demodulation         : 0.05
% 2.55/1.33  BG Simplification    : 0.01
% 2.55/1.33  Subsumption          : 0.06
% 2.55/1.33  Abstraction          : 0.01
% 2.55/1.33  MUC search           : 0.00
% 2.55/1.33  Cooper               : 0.00
% 2.55/1.33  Total                : 0.60
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
