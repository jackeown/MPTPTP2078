%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:01 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 152 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_55,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_71,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_148,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_157,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_148])).

tff(c_224,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_224])).

tff(c_235,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_157,c_231])).

tff(c_236,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_235])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_183,plain,(
    ! [B_75,A_76] :
      ( r2_hidden(k1_funct_1(B_75,A_76),k2_relat_1(B_75))
      | ~ r2_hidden(A_76,k1_relat_1(B_75))
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    ! [B_106,A_107,A_108] :
      ( r2_hidden(k1_funct_1(B_106,A_107),A_108)
      | ~ m1_subset_1(k2_relat_1(B_106),k1_zfmisc_1(A_108))
      | ~ r2_hidden(A_107,k1_relat_1(B_106))
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_290,plain,(
    ! [B_109,A_110,B_111] :
      ( r2_hidden(k1_funct_1(B_109,A_110),B_111)
      | ~ r2_hidden(A_110,k1_relat_1(B_109))
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109)
      | ~ r1_tarski(k2_relat_1(B_109),B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_295,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_290,c_34])).

tff(c_299,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44,c_38,c_236,c_295])).

tff(c_302,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_299])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_80,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.30/1.35  
% 2.30/1.35  %Foreground sorts:
% 2.30/1.35  
% 2.30/1.35  
% 2.30/1.35  %Background operators:
% 2.30/1.35  
% 2.30/1.35  
% 2.30/1.35  %Foreground operators:
% 2.30/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.30/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.30/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.30/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.30/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.35  
% 2.30/1.36  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.30/1.36  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.30/1.36  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.30/1.36  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.30/1.36  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.30/1.36  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.30/1.36  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.30/1.36  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.30/1.36  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.30/1.36  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.36  tff(c_55, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.30/1.36  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_55])).
% 2.30/1.36  tff(c_71, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.30/1.36  tff(c_80, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_71])).
% 2.30/1.36  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.36  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.36  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.36  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.36  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.36  tff(c_148, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.30/1.36  tff(c_157, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_148])).
% 2.30/1.36  tff(c_224, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.30/1.36  tff(c_231, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_224])).
% 2.30/1.36  tff(c_235, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_157, c_231])).
% 2.30/1.36  tff(c_236, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_36, c_235])).
% 2.30/1.36  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.30/1.36  tff(c_183, plain, (![B_75, A_76]: (r2_hidden(k1_funct_1(B_75, A_76), k2_relat_1(B_75)) | ~r2_hidden(A_76, k1_relat_1(B_75)) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.36  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.30/1.36  tff(c_285, plain, (![B_106, A_107, A_108]: (r2_hidden(k1_funct_1(B_106, A_107), A_108) | ~m1_subset_1(k2_relat_1(B_106), k1_zfmisc_1(A_108)) | ~r2_hidden(A_107, k1_relat_1(B_106)) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_183, c_2])).
% 2.30/1.36  tff(c_290, plain, (![B_109, A_110, B_111]: (r2_hidden(k1_funct_1(B_109, A_110), B_111) | ~r2_hidden(A_110, k1_relat_1(B_109)) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109) | ~r1_tarski(k2_relat_1(B_109), B_111))), inference(resolution, [status(thm)], [c_6, c_285])).
% 2.30/1.36  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.30/1.36  tff(c_295, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_290, c_34])).
% 2.30/1.36  tff(c_299, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44, c_38, c_236, c_295])).
% 2.30/1.36  tff(c_302, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_299])).
% 2.30/1.36  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_80, c_302])).
% 2.30/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.36  
% 2.30/1.36  Inference rules
% 2.30/1.36  ----------------------
% 2.30/1.36  #Ref     : 0
% 2.30/1.36  #Sup     : 50
% 2.30/1.36  #Fact    : 0
% 2.30/1.36  #Define  : 0
% 2.30/1.36  #Split   : 1
% 2.30/1.36  #Chain   : 0
% 2.30/1.36  #Close   : 0
% 2.30/1.36  
% 2.30/1.36  Ordering : KBO
% 2.30/1.36  
% 2.30/1.36  Simplification rules
% 2.30/1.36  ----------------------
% 2.30/1.36  #Subsume      : 0
% 2.30/1.36  #Demod        : 18
% 2.30/1.36  #Tautology    : 15
% 2.30/1.36  #SimpNegUnit  : 4
% 2.30/1.36  #BackRed      : 1
% 2.30/1.36  
% 2.30/1.36  #Partial instantiations: 0
% 2.30/1.36  #Strategies tried      : 1
% 2.30/1.36  
% 2.30/1.36  Timing (in seconds)
% 2.30/1.36  ----------------------
% 2.30/1.36  Preprocessing        : 0.33
% 2.30/1.36  Parsing              : 0.18
% 2.30/1.36  CNF conversion       : 0.02
% 2.30/1.36  Main loop            : 0.22
% 2.30/1.36  Inferencing          : 0.08
% 2.30/1.36  Reduction            : 0.06
% 2.30/1.36  Demodulation         : 0.04
% 2.30/1.36  BG Simplification    : 0.01
% 2.30/1.36  Subsumption          : 0.04
% 2.30/1.36  Abstraction          : 0.01
% 2.30/1.36  MUC search           : 0.00
% 2.30/1.36  Cooper               : 0.00
% 2.30/1.36  Total                : 0.58
% 2.30/1.36  Index Insertion      : 0.00
% 2.30/1.36  Index Deletion       : 0.00
% 2.30/1.37  Index Matching       : 0.00
% 2.30/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
