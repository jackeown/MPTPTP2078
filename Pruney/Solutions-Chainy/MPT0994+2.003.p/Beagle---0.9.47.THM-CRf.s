%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 150 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( r2_hidden(C,A)
            & r2_hidden(k1_funct_1(E,C),D) )
         => ( B = k1_xboole_0
            | k1_funct_1(k6_relset_1(A,B,D,E),C) = k1_funct_1(E,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
       => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_61,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k6_relset_1(A_30,B_31,C_32,D_33) = k8_relat_1(C_32,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ! [C_32] : k6_relset_1('#skF_1','#skF_2',C_32,'#skF_5') = k8_relat_1(C_32,'#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_61])).

tff(c_30,plain,(
    k1_funct_1(k6_relset_1('#skF_1','#skF_2','#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_65,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_87,plain,(
    ! [B_50,A_51,C_52] :
      ( k1_xboole_0 = B_50
      | k1_relset_1(A_51,B_50,C_52) = A_51
      | ~ v1_funct_2(C_52,A_51,B_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_93,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56,c_90])).

tff(c_94,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_93])).

tff(c_34,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_105,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden(A_56,k1_relat_1(k8_relat_1(B_57,C_58)))
      | ~ r2_hidden(k1_funct_1(C_58,A_56),B_57)
      | ~ r2_hidden(A_56,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [B_10,C_11,A_9] :
      ( k1_funct_1(k8_relat_1(B_10,C_11),A_9) = k1_funct_1(C_11,A_9)
      | ~ r2_hidden(A_9,k1_relat_1(k8_relat_1(B_10,C_11)))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_118,plain,(
    ! [B_59,C_60,A_61] :
      ( k1_funct_1(k8_relat_1(B_59,C_60),A_61) = k1_funct_1(C_60,A_61)
      | ~ r2_hidden(k1_funct_1(C_60,A_61),B_59)
      | ~ r2_hidden(A_61,k1_relat_1(C_60))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_125,plain,
    ( k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_129,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_36,c_94,c_125])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.21  
% 2.13/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.22  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.13/1.22  
% 2.13/1.22  %Foreground sorts:
% 2.13/1.22  
% 2.13/1.22  
% 2.13/1.22  %Background operators:
% 2.13/1.22  
% 2.13/1.22  
% 2.13/1.22  %Foreground operators:
% 2.13/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.13/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.22  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.22  
% 2.13/1.23  tff(f_93, negated_conjecture, ~(![A, B, C, D, E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r2_hidden(C, A) & r2_hidden(k1_funct_1(E, C), D)) => ((B = k1_xboole_0) | (k1_funct_1(k6_relset_1(A, B, D, E), C) = k1_funct_1(E, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_funct_2)).
% 2.13/1.23  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.13/1.23  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.13/1.23  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.13/1.23  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.13/1.23  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.13/1.23  tff(f_44, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.13/1.23  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 2.13/1.23  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_61, plain, (![A_30, B_31, C_32, D_33]: (k6_relset_1(A_30, B_31, C_32, D_33)=k8_relat_1(C_32, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.23  tff(c_64, plain, (![C_32]: (k6_relset_1('#skF_1', '#skF_2', C_32, '#skF_5')=k8_relat_1(C_32, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_61])).
% 2.13/1.23  tff(c_30, plain, (k1_funct_1(k6_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_65, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 2.13/1.23  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.13/1.23  tff(c_44, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.23  tff(c_47, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_44])).
% 2.13/1.23  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 2.13/1.23  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_52, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.23  tff(c_56, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_52])).
% 2.13/1.23  tff(c_87, plain, (![B_50, A_51, C_52]: (k1_xboole_0=B_50 | k1_relset_1(A_51, B_50, C_52)=A_51 | ~v1_funct_2(C_52, A_51, B_50) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.23  tff(c_90, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.13/1.23  tff(c_93, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56, c_90])).
% 2.13/1.23  tff(c_94, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_32, c_93])).
% 2.13/1.23  tff(c_34, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.23  tff(c_105, plain, (![A_56, B_57, C_58]: (r2_hidden(A_56, k1_relat_1(k8_relat_1(B_57, C_58))) | ~r2_hidden(k1_funct_1(C_58, A_56), B_57) | ~r2_hidden(A_56, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.23  tff(c_12, plain, (![B_10, C_11, A_9]: (k1_funct_1(k8_relat_1(B_10, C_11), A_9)=k1_funct_1(C_11, A_9) | ~r2_hidden(A_9, k1_relat_1(k8_relat_1(B_10, C_11))) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.23  tff(c_118, plain, (![B_59, C_60, A_61]: (k1_funct_1(k8_relat_1(B_59, C_60), A_61)=k1_funct_1(C_60, A_61) | ~r2_hidden(k1_funct_1(C_60, A_61), B_59) | ~r2_hidden(A_61, k1_relat_1(C_60)) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_105, c_12])).
% 2.13/1.23  tff(c_125, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.13/1.23  tff(c_129, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_36, c_94, c_125])).
% 2.13/1.23  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_129])).
% 2.13/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.23  
% 2.13/1.23  Inference rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Ref     : 0
% 2.13/1.23  #Sup     : 18
% 2.13/1.23  #Fact    : 0
% 2.13/1.23  #Define  : 0
% 2.13/1.23  #Split   : 0
% 2.13/1.23  #Chain   : 0
% 2.13/1.23  #Close   : 0
% 2.13/1.23  
% 2.13/1.23  Ordering : KBO
% 2.13/1.23  
% 2.13/1.23  Simplification rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Subsume      : 0
% 2.13/1.23  #Demod        : 11
% 2.13/1.23  #Tautology    : 11
% 2.13/1.23  #SimpNegUnit  : 3
% 2.13/1.23  #BackRed      : 2
% 2.13/1.23  
% 2.13/1.23  #Partial instantiations: 0
% 2.13/1.23  #Strategies tried      : 1
% 2.13/1.23  
% 2.13/1.23  Timing (in seconds)
% 2.13/1.23  ----------------------
% 2.13/1.23  Preprocessing        : 0.31
% 2.13/1.23  Parsing              : 0.17
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.23  Main loop            : 0.14
% 2.13/1.23  Inferencing          : 0.05
% 2.13/1.23  Reduction            : 0.05
% 2.13/1.23  Demodulation         : 0.03
% 2.13/1.23  BG Simplification    : 0.01
% 2.13/1.23  Subsumption          : 0.02
% 2.13/1.23  Abstraction          : 0.01
% 2.13/1.23  MUC search           : 0.00
% 2.13/1.23  Cooper               : 0.00
% 2.13/1.23  Total                : 0.49
% 2.13/1.23  Index Insertion      : 0.00
% 2.13/1.23  Index Deletion       : 0.00
% 2.13/1.23  Index Matching       : 0.00
% 2.13/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
