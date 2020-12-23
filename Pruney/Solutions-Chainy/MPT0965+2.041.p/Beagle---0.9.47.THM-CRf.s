%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:05 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   60 (  78 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 163 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    ! [C_28,B_29,A_30] :
      ( v5_relat_1(C_28,B_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_30,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_55,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_84,plain,(
    ! [B_47,A_48,C_49] :
      ( k1_xboole_0 = B_47
      | k1_relset_1(A_48,B_47,C_49) = A_48
      | ~ v1_funct_2(C_49,A_48,B_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_87,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70,c_87])).

tff(c_91,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_90])).

tff(c_10,plain,(
    ! [C_11,B_10,A_9] :
      ( m1_subset_1(k1_funct_1(C_11,B_10),A_9)
      | ~ r2_hidden(B_10,k1_relat_1(C_11))
      | ~ v1_funct_1(C_11)
      | ~ v5_relat_1(C_11,A_9)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_10),A_9)
      | ~ r2_hidden(B_10,'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_9)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_112,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_53),A_54)
      | ~ r2_hidden(B_53,'#skF_1')
      | ~ v5_relat_1('#skF_4',A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_40,c_102])).

tff(c_43,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_47,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_30])).

tff(c_48,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_151,plain,
    ( ~ r2_hidden('#skF_3','#skF_1')
    | ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_48])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34,c_151])).

tff(c_165,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.29  
% 1.95/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.29  
% 1.95/1.29  %Foreground sorts:
% 1.95/1.29  
% 1.95/1.29  
% 1.95/1.29  %Background operators:
% 1.95/1.29  
% 1.95/1.29  
% 1.95/1.29  %Foreground operators:
% 1.95/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.95/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.95/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.95/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.95/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.29  
% 1.95/1.30  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.95/1.30  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.95/1.30  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.95/1.30  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.95/1.30  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.95/1.30  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.95/1.30  tff(f_54, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 1.95/1.30  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.95/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.95/1.30  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 1.95/1.30  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 1.95/1.30  tff(c_56, plain, (![C_28, B_29, A_30]: (v5_relat_1(C_28, B_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_30, B_29))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.30  tff(c_60, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_56])).
% 1.95/1.30  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 1.95/1.30  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.30  tff(c_49, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.95/1.30  tff(c_52, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_49])).
% 1.95/1.30  tff(c_55, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_52])).
% 1.95/1.30  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 1.95/1.30  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 1.95/1.30  tff(c_66, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.30  tff(c_70, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_66])).
% 1.95/1.30  tff(c_84, plain, (![B_47, A_48, C_49]: (k1_xboole_0=B_47 | k1_relset_1(A_48, B_47, C_49)=A_48 | ~v1_funct_2(C_49, A_48, B_47) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.95/1.30  tff(c_87, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_84])).
% 1.95/1.30  tff(c_90, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_70, c_87])).
% 1.95/1.30  tff(c_91, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_32, c_90])).
% 1.95/1.30  tff(c_10, plain, (![C_11, B_10, A_9]: (m1_subset_1(k1_funct_1(C_11, B_10), A_9) | ~r2_hidden(B_10, k1_relat_1(C_11)) | ~v1_funct_1(C_11) | ~v5_relat_1(C_11, A_9) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.30  tff(c_102, plain, (![B_10, A_9]: (m1_subset_1(k1_funct_1('#skF_4', B_10), A_9) | ~r2_hidden(B_10, '#skF_1') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_9) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 1.95/1.30  tff(c_112, plain, (![B_53, A_54]: (m1_subset_1(k1_funct_1('#skF_4', B_53), A_54) | ~r2_hidden(B_53, '#skF_1') | ~v5_relat_1('#skF_4', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_40, c_102])).
% 1.95/1.30  tff(c_43, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | v1_xboole_0(B_25) | ~m1_subset_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.30  tff(c_30, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 1.95/1.30  tff(c_47, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_43, c_30])).
% 1.95/1.30  tff(c_48, plain, (~m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_47])).
% 1.95/1.30  tff(c_151, plain, (~r2_hidden('#skF_3', '#skF_1') | ~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_112, c_48])).
% 1.95/1.30  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_34, c_151])).
% 1.95/1.30  tff(c_165, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_47])).
% 1.95/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.30  tff(c_169, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_165, c_2])).
% 1.95/1.30  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_169])).
% 1.95/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  Inference rules
% 1.95/1.30  ----------------------
% 1.95/1.30  #Ref     : 0
% 1.95/1.30  #Sup     : 26
% 1.95/1.30  #Fact    : 0
% 1.95/1.30  #Define  : 0
% 1.95/1.30  #Split   : 1
% 1.95/1.30  #Chain   : 0
% 1.95/1.30  #Close   : 0
% 1.95/1.30  
% 1.95/1.30  Ordering : KBO
% 1.95/1.30  
% 1.95/1.30  Simplification rules
% 1.95/1.30  ----------------------
% 1.95/1.30  #Subsume      : 0
% 1.95/1.30  #Demod        : 10
% 1.95/1.30  #Tautology    : 7
% 1.95/1.30  #SimpNegUnit  : 3
% 1.95/1.30  #BackRed      : 1
% 1.95/1.30  
% 1.95/1.30  #Partial instantiations: 0
% 1.95/1.30  #Strategies tried      : 1
% 1.95/1.30  
% 1.95/1.30  Timing (in seconds)
% 1.95/1.30  ----------------------
% 1.95/1.31  Preprocessing        : 0.33
% 1.95/1.31  Parsing              : 0.18
% 1.95/1.31  CNF conversion       : 0.02
% 1.95/1.31  Main loop            : 0.16
% 1.95/1.31  Inferencing          : 0.06
% 1.95/1.31  Reduction            : 0.05
% 1.95/1.31  Demodulation         : 0.04
% 1.95/1.31  BG Simplification    : 0.01
% 1.95/1.31  Subsumption          : 0.02
% 1.95/1.31  Abstraction          : 0.01
% 1.95/1.31  MUC search           : 0.00
% 1.95/1.31  Cooper               : 0.00
% 1.95/1.31  Total                : 0.51
% 1.95/1.31  Index Insertion      : 0.00
% 1.95/1.31  Index Deletion       : 0.00
% 1.95/1.31  Index Matching       : 0.00
% 1.95/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
