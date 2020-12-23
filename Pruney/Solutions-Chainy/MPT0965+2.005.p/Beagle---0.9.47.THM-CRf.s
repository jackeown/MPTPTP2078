%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:01 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 143 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_59,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_107,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_132,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_135,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_132])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_111,c_135])).

tff(c_139,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_138])).

tff(c_117,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(k1_funct_1(B_54,A_55),k2_relat_1(B_54))
      | ~ r2_hidden(A_55,k1_relat_1(B_54))
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [B_74,A_75,B_76] :
      ( r2_hidden(k1_funct_1(B_74,A_75),B_76)
      | ~ r1_tarski(k2_relat_1(B_74),B_76)
      | ~ r2_hidden(A_75,k1_relat_1(B_74))
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_162,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_34])).

tff(c_166,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_38,c_139,c_162])).

tff(c_169,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_63,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:12:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.22  
% 2.09/1.22  %Foreground sorts:
% 2.09/1.22  
% 2.09/1.22  
% 2.09/1.22  %Background operators:
% 2.09/1.22  
% 2.09/1.22  
% 2.09/1.22  %Foreground operators:
% 2.09/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.09/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.09/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.09/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.09/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.22  
% 2.18/1.23  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.18/1.23  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.18/1.23  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.18/1.23  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.18/1.23  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.23  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.18/1.23  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.18/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.18/1.23  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.23  tff(c_46, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.23  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_46])).
% 2.18/1.23  tff(c_59, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.23  tff(c_63, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_59])).
% 2.18/1.23  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.23  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.23  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.23  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.23  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.23  tff(c_107, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.23  tff(c_111, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.18/1.23  tff(c_132, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.23  tff(c_135, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_132])).
% 2.18/1.23  tff(c_138, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_111, c_135])).
% 2.18/1.23  tff(c_139, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_138])).
% 2.18/1.23  tff(c_117, plain, (![B_54, A_55]: (r2_hidden(k1_funct_1(B_54, A_55), k2_relat_1(B_54)) | ~r2_hidden(A_55, k1_relat_1(B_54)) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.23  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.23  tff(c_157, plain, (![B_74, A_75, B_76]: (r2_hidden(k1_funct_1(B_74, A_75), B_76) | ~r1_tarski(k2_relat_1(B_74), B_76) | ~r2_hidden(A_75, k1_relat_1(B_74)) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_117, c_2])).
% 2.18/1.23  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.23  tff(c_162, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~r2_hidden('#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_157, c_34])).
% 2.18/1.23  tff(c_166, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_38, c_139, c_162])).
% 2.18/1.23  tff(c_169, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_166])).
% 2.18/1.23  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_63, c_169])).
% 2.18/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.23  
% 2.18/1.23  Inference rules
% 2.18/1.23  ----------------------
% 2.18/1.23  #Ref     : 0
% 2.18/1.23  #Sup     : 28
% 2.18/1.23  #Fact    : 0
% 2.18/1.23  #Define  : 0
% 2.18/1.23  #Split   : 0
% 2.18/1.23  #Chain   : 0
% 2.18/1.23  #Close   : 0
% 2.18/1.23  
% 2.18/1.23  Ordering : KBO
% 2.18/1.23  
% 2.18/1.23  Simplification rules
% 2.18/1.23  ----------------------
% 2.18/1.23  #Subsume      : 2
% 2.18/1.23  #Demod        : 11
% 2.18/1.23  #Tautology    : 9
% 2.18/1.23  #SimpNegUnit  : 2
% 2.18/1.23  #BackRed      : 1
% 2.18/1.23  
% 2.18/1.23  #Partial instantiations: 0
% 2.18/1.23  #Strategies tried      : 1
% 2.18/1.23  
% 2.18/1.23  Timing (in seconds)
% 2.18/1.23  ----------------------
% 2.18/1.24  Preprocessing        : 0.30
% 2.18/1.24  Parsing              : 0.16
% 2.18/1.24  CNF conversion       : 0.02
% 2.18/1.24  Main loop            : 0.18
% 2.18/1.24  Inferencing          : 0.07
% 2.18/1.24  Reduction            : 0.05
% 2.18/1.24  Demodulation         : 0.04
% 2.18/1.24  BG Simplification    : 0.01
% 2.18/1.24  Subsumption          : 0.03
% 2.18/1.24  Abstraction          : 0.01
% 2.18/1.24  MUC search           : 0.00
% 2.18/1.24  Cooper               : 0.00
% 2.18/1.24  Total                : 0.51
% 2.18/1.24  Index Insertion      : 0.00
% 2.18/1.24  Index Deletion       : 0.00
% 2.18/1.24  Index Matching       : 0.00
% 2.18/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
