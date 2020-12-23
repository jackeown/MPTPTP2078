%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:01 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 123 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_74,plain,(
    ! [C_41,B_42,A_43] :
      ( v5_relat_1(C_41,B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_74])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_95,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_relset_1(A_49,B_50,C_51) = k2_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_105,plain,(
    ! [D_54,C_55,A_56,B_57] :
      ( r2_hidden(k1_funct_1(D_54,C_55),k2_relset_1(A_56,B_57,D_54))
      | k1_xboole_0 = B_57
      | ~ r2_hidden(C_55,A_56)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_2(D_54,A_56,B_57)
      | ~ v1_funct_1(D_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,(
    ! [C_55] :
      ( r2_hidden(k1_funct_1('#skF_5',C_55),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_55,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_105])).

tff(c_113,plain,(
    ! [C_55] :
      ( r2_hidden(k1_funct_1('#skF_5',C_55),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_110])).

tff(c_115,plain,(
    ! [C_58] :
      ( r2_hidden(k1_funct_1('#skF_5',C_58),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_58,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_113])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [C_59,B_60] :
      ( r2_hidden(k1_funct_1('#skF_5',C_59),B_60)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_60)
      | ~ r2_hidden(C_59,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_22,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_124,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_22])).

tff(c_128,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_124])).

tff(c_131,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_78,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:22:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.02/1.22  
% 2.02/1.22  %Foreground sorts:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Background operators:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Foreground operators:
% 2.02/1.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.02/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.02/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.22  
% 2.02/1.24  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.02/1.24  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.02/1.24  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.02/1.24  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.02/1.24  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.02/1.24  tff(f_64, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.02/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.24  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.24  tff(c_34, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.24  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.02/1.24  tff(c_74, plain, (![C_41, B_42, A_43]: (v5_relat_1(C_41, B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.24  tff(c_78, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_74])).
% 2.02/1.24  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.24  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.24  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.24  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.24  tff(c_30, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.24  tff(c_95, plain, (![A_49, B_50, C_51]: (k2_relset_1(A_49, B_50, C_51)=k2_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.24  tff(c_99, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_95])).
% 2.02/1.24  tff(c_105, plain, (![D_54, C_55, A_56, B_57]: (r2_hidden(k1_funct_1(D_54, C_55), k2_relset_1(A_56, B_57, D_54)) | k1_xboole_0=B_57 | ~r2_hidden(C_55, A_56) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_2(D_54, A_56, B_57) | ~v1_funct_1(D_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.02/1.24  tff(c_110, plain, (![C_55]: (r2_hidden(k1_funct_1('#skF_5', C_55), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_55, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_105])).
% 2.02/1.24  tff(c_113, plain, (![C_55]: (r2_hidden(k1_funct_1('#skF_5', C_55), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_110])).
% 2.02/1.24  tff(c_115, plain, (![C_58]: (r2_hidden(k1_funct_1('#skF_5', C_58), k2_relat_1('#skF_5')) | ~r2_hidden(C_58, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_113])).
% 2.02/1.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.24  tff(c_119, plain, (![C_59, B_60]: (r2_hidden(k1_funct_1('#skF_5', C_59), B_60) | ~r1_tarski(k2_relat_1('#skF_5'), B_60) | ~r2_hidden(C_59, '#skF_2'))), inference(resolution, [status(thm)], [c_115, c_2])).
% 2.02/1.24  tff(c_22, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.24  tff(c_124, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_119, c_22])).
% 2.02/1.24  tff(c_128, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_124])).
% 2.02/1.24  tff(c_131, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_128])).
% 2.02/1.24  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_78, c_131])).
% 2.02/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  Inference rules
% 2.02/1.24  ----------------------
% 2.02/1.24  #Ref     : 0
% 2.02/1.24  #Sup     : 22
% 2.02/1.24  #Fact    : 0
% 2.02/1.24  #Define  : 0
% 2.02/1.24  #Split   : 0
% 2.02/1.24  #Chain   : 0
% 2.02/1.24  #Close   : 0
% 2.02/1.24  
% 2.02/1.24  Ordering : KBO
% 2.02/1.24  
% 2.02/1.24  Simplification rules
% 2.02/1.24  ----------------------
% 2.02/1.24  #Subsume      : 1
% 2.02/1.24  #Demod        : 6
% 2.02/1.24  #Tautology    : 4
% 2.02/1.24  #SimpNegUnit  : 1
% 2.02/1.24  #BackRed      : 0
% 2.02/1.24  
% 2.02/1.24  #Partial instantiations: 0
% 2.02/1.24  #Strategies tried      : 1
% 2.02/1.24  
% 2.02/1.24  Timing (in seconds)
% 2.02/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.31
% 2.12/1.24  Parsing              : 0.17
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.16
% 2.12/1.24  Inferencing          : 0.07
% 2.12/1.24  Reduction            : 0.04
% 2.12/1.24  Demodulation         : 0.03
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.03
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.50
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
