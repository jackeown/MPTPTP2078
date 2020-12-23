%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 104 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 278 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [A_18] :
      ( m1_subset_1(A_18,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18))))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2506,plain,(
    ! [D_245,C_246,B_247,A_248] :
      ( m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(C_246,B_247)))
      | ~ r1_tarski(k2_relat_1(D_245),B_247)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(C_246,A_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2892,plain,(
    ! [A_298,B_299] :
      ( m1_subset_1(A_298,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_298),B_299)))
      | ~ r1_tarski(k2_relat_1(A_298),B_299)
      | ~ v1_funct_1(A_298)
      | ~ v1_relat_1(A_298) ) ),
    inference(resolution,[status(thm)],[c_36,c_2506])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42])).

tff(c_86,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_208,plain,(
    ! [D_48,C_49,B_50,A_51] :
      ( m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(C_49,B_50)))
      | ~ r1_tarski(k2_relat_1(D_48),B_50)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(C_49,A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_509,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(A_94,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94),B_95)))
      | ~ r1_tarski(k2_relat_1(A_94),B_95)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_36,c_208])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1197,plain,(
    ! [A_150,B_151] :
      ( k1_relset_1(k1_relat_1(A_150),B_151,A_150) = k1_relat_1(A_150)
      | ~ r1_tarski(k2_relat_1(A_150),B_151)
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_509,c_20])).

tff(c_1213,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1197])).

tff(c_1225,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1213])).

tff(c_30,plain,(
    ! [B_16,C_17,A_15] :
      ( k1_xboole_0 = B_16
      | v1_funct_2(C_17,A_15,B_16)
      | k1_relset_1(A_15,B_16,C_17) != A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2210,plain,(
    ! [B_217,A_218] :
      ( k1_xboole_0 = B_217
      | v1_funct_2(A_218,k1_relat_1(A_218),B_217)
      | k1_relset_1(k1_relat_1(A_218),B_217,A_218) != k1_relat_1(A_218)
      | ~ r1_tarski(k2_relat_1(A_218),B_217)
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_509,c_30])).

tff(c_2229,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2210,c_86])).

tff(c_2243,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1225,c_2229])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2312,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2243,c_8])).

tff(c_98,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_124,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_2319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2312,c_124])).

tff(c_2320,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_2345,plain,(
    ! [A_220] :
      ( v1_funct_2(A_220,k1_relat_1(A_220),k2_relat_1(A_220))
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2348,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2320,c_2345])).

tff(c_2350,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2348])).

tff(c_2352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2350])).

tff(c_2353,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2906,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2892,c_2353])).

tff(c_2921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.80  
% 4.48/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.80  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.48/1.80  
% 4.48/1.80  %Foreground sorts:
% 4.48/1.80  
% 4.48/1.80  
% 4.48/1.80  %Background operators:
% 4.48/1.80  
% 4.48/1.80  
% 4.48/1.80  %Foreground operators:
% 4.48/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.48/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.48/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.48/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.48/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.48/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.48/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.48/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.48/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.80  
% 4.48/1.81  tff(f_94, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.48/1.81  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.48/1.81  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 4.48/1.81  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.48/1.81  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.48/1.81  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.48/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.48/1.81  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.48/1.81  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.48/1.81  tff(c_44, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.48/1.81  tff(c_36, plain, (![A_18]: (m1_subset_1(A_18, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18)))) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.48/1.81  tff(c_2506, plain, (![D_245, C_246, B_247, A_248]: (m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(C_246, B_247))) | ~r1_tarski(k2_relat_1(D_245), B_247) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(C_246, A_248))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.48/1.81  tff(c_2892, plain, (![A_298, B_299]: (m1_subset_1(A_298, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_298), B_299))) | ~r1_tarski(k2_relat_1(A_298), B_299) | ~v1_funct_1(A_298) | ~v1_relat_1(A_298))), inference(resolution, [status(thm)], [c_36, c_2506])).
% 4.48/1.81  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.48/1.81  tff(c_50, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42])).
% 4.48/1.81  tff(c_86, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.48/1.81  tff(c_208, plain, (![D_48, C_49, B_50, A_51]: (m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(C_49, B_50))) | ~r1_tarski(k2_relat_1(D_48), B_50) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(C_49, A_51))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.48/1.81  tff(c_509, plain, (![A_94, B_95]: (m1_subset_1(A_94, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94), B_95))) | ~r1_tarski(k2_relat_1(A_94), B_95) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_36, c_208])).
% 4.48/1.81  tff(c_20, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.48/1.81  tff(c_1197, plain, (![A_150, B_151]: (k1_relset_1(k1_relat_1(A_150), B_151, A_150)=k1_relat_1(A_150) | ~r1_tarski(k2_relat_1(A_150), B_151) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_509, c_20])).
% 4.48/1.81  tff(c_1213, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1197])).
% 4.48/1.81  tff(c_1225, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1213])).
% 4.48/1.81  tff(c_30, plain, (![B_16, C_17, A_15]: (k1_xboole_0=B_16 | v1_funct_2(C_17, A_15, B_16) | k1_relset_1(A_15, B_16, C_17)!=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.81  tff(c_2210, plain, (![B_217, A_218]: (k1_xboole_0=B_217 | v1_funct_2(A_218, k1_relat_1(A_218), B_217) | k1_relset_1(k1_relat_1(A_218), B_217, A_218)!=k1_relat_1(A_218) | ~r1_tarski(k2_relat_1(A_218), B_217) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_509, c_30])).
% 4.48/1.81  tff(c_2229, plain, (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2210, c_86])).
% 4.48/1.81  tff(c_2243, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1225, c_2229])).
% 4.48/1.81  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.81  tff(c_2312, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2243, c_8])).
% 4.48/1.81  tff(c_98, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.48/1.81  tff(c_105, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_98])).
% 4.48/1.81  tff(c_124, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_105])).
% 4.48/1.81  tff(c_2319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2312, c_124])).
% 4.48/1.81  tff(c_2320, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_105])).
% 4.48/1.81  tff(c_2345, plain, (![A_220]: (v1_funct_2(A_220, k1_relat_1(A_220), k2_relat_1(A_220)) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.48/1.81  tff(c_2348, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2320, c_2345])).
% 4.48/1.81  tff(c_2350, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2348])).
% 4.48/1.81  tff(c_2352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2350])).
% 4.48/1.81  tff(c_2353, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 4.48/1.81  tff(c_2906, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2892, c_2353])).
% 4.48/1.81  tff(c_2921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2906])).
% 4.48/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.81  
% 4.48/1.81  Inference rules
% 4.48/1.81  ----------------------
% 4.48/1.81  #Ref     : 0
% 4.48/1.81  #Sup     : 618
% 4.48/1.81  #Fact    : 0
% 4.48/1.81  #Define  : 0
% 4.48/1.81  #Split   : 11
% 4.48/1.81  #Chain   : 0
% 4.48/1.81  #Close   : 0
% 4.48/1.81  
% 4.48/1.81  Ordering : KBO
% 4.48/1.81  
% 4.48/1.81  Simplification rules
% 4.48/1.81  ----------------------
% 4.48/1.81  #Subsume      : 122
% 4.48/1.81  #Demod        : 590
% 4.48/1.81  #Tautology    : 275
% 4.48/1.81  #SimpNegUnit  : 12
% 4.48/1.81  #BackRed      : 74
% 4.48/1.81  
% 4.48/1.81  #Partial instantiations: 0
% 4.48/1.81  #Strategies tried      : 1
% 4.48/1.81  
% 4.48/1.81  Timing (in seconds)
% 4.48/1.81  ----------------------
% 4.48/1.82  Preprocessing        : 0.29
% 4.48/1.82  Parsing              : 0.15
% 4.48/1.82  CNF conversion       : 0.02
% 4.48/1.82  Main loop            : 0.74
% 4.48/1.82  Inferencing          : 0.25
% 4.48/1.82  Reduction            : 0.23
% 4.48/1.82  Demodulation         : 0.16
% 4.48/1.82  BG Simplification    : 0.03
% 4.48/1.82  Subsumption          : 0.17
% 4.48/1.82  Abstraction          : 0.04
% 4.48/1.82  MUC search           : 0.00
% 4.48/1.82  Cooper               : 0.00
% 4.48/1.82  Total                : 1.06
% 4.48/1.82  Index Insertion      : 0.00
% 4.48/1.82  Index Deletion       : 0.00
% 4.48/1.82  Index Matching       : 0.00
% 4.48/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
