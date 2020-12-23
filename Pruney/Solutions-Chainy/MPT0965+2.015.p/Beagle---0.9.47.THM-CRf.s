%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   82 ( 140 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
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

tff(c_55,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

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

tff(c_129,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_129])).

tff(c_508,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_xboole_0 = B_119
      | k1_relset_1(A_120,B_119,C_121) = A_120
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_519,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_508])).

tff(c_524,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_138,c_519])).

tff(c_525,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_524])).

tff(c_119,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_158,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1(k2_relset_1(A_62,B_63,C_64),k1_zfmisc_1(B_63))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_158])).

tff(c_182,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_176])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_186,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_8])).

tff(c_247,plain,(
    ! [B_77,A_78] :
      ( r2_hidden(k1_funct_1(B_77,A_78),k2_relat_1(B_77))
      | ~ r2_hidden(A_78,k1_relat_1(B_77))
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1046,plain,(
    ! [B_197,A_198,B_199] :
      ( r2_hidden(k1_funct_1(B_197,A_198),B_199)
      | ~ r1_tarski(k2_relat_1(B_197),B_199)
      | ~ r2_hidden(A_198,k1_relat_1(B_197))
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(resolution,[status(thm)],[c_247,c_2])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1051,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1046,c_34])).

tff(c_1056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44,c_38,c_525,c_186,c_1051])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:27:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.63  
% 3.54/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.64  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.54/1.64  
% 3.54/1.64  %Foreground sorts:
% 3.54/1.64  
% 3.54/1.64  
% 3.54/1.64  %Background operators:
% 3.54/1.64  
% 3.54/1.64  
% 3.54/1.64  %Foreground operators:
% 3.54/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.54/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.54/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.54/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.64  
% 3.54/1.65  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.54/1.65  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.54/1.65  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.54/1.65  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.54/1.65  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.54/1.65  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.54/1.65  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.54/1.65  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.54/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.54/1.65  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.54/1.65  tff(c_55, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.65  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_55])).
% 3.54/1.65  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.54/1.65  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.54/1.65  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.54/1.65  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.54/1.65  tff(c_129, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.54/1.65  tff(c_138, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_129])).
% 3.54/1.65  tff(c_508, plain, (![B_119, A_120, C_121]: (k1_xboole_0=B_119 | k1_relset_1(A_120, B_119, C_121)=A_120 | ~v1_funct_2(C_121, A_120, B_119) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.54/1.65  tff(c_519, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_508])).
% 3.54/1.65  tff(c_524, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_138, c_519])).
% 3.54/1.65  tff(c_525, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_524])).
% 3.54/1.65  tff(c_119, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.54/1.65  tff(c_128, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_119])).
% 3.54/1.65  tff(c_158, plain, (![A_62, B_63, C_64]: (m1_subset_1(k2_relset_1(A_62, B_63, C_64), k1_zfmisc_1(B_63)) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.54/1.65  tff(c_176, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_158])).
% 3.54/1.65  tff(c_182, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_176])).
% 3.54/1.65  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.54/1.65  tff(c_186, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_182, c_8])).
% 3.54/1.65  tff(c_247, plain, (![B_77, A_78]: (r2_hidden(k1_funct_1(B_77, A_78), k2_relat_1(B_77)) | ~r2_hidden(A_78, k1_relat_1(B_77)) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.54/1.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.65  tff(c_1046, plain, (![B_197, A_198, B_199]: (r2_hidden(k1_funct_1(B_197, A_198), B_199) | ~r1_tarski(k2_relat_1(B_197), B_199) | ~r2_hidden(A_198, k1_relat_1(B_197)) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(resolution, [status(thm)], [c_247, c_2])).
% 3.54/1.65  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.54/1.65  tff(c_1051, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~r2_hidden('#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1046, c_34])).
% 3.54/1.65  tff(c_1056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_44, c_38, c_525, c_186, c_1051])).
% 3.54/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.65  
% 3.54/1.65  Inference rules
% 3.54/1.65  ----------------------
% 3.54/1.65  #Ref     : 0
% 3.54/1.65  #Sup     : 209
% 3.54/1.65  #Fact    : 0
% 3.54/1.65  #Define  : 0
% 3.54/1.65  #Split   : 7
% 3.54/1.65  #Chain   : 0
% 3.54/1.65  #Close   : 0
% 3.54/1.65  
% 3.54/1.65  Ordering : KBO
% 3.54/1.65  
% 3.54/1.65  Simplification rules
% 3.54/1.65  ----------------------
% 3.54/1.65  #Subsume      : 15
% 3.54/1.65  #Demod        : 52
% 3.54/1.65  #Tautology    : 49
% 3.54/1.65  #SimpNegUnit  : 8
% 3.54/1.65  #BackRed      : 1
% 3.54/1.65  
% 3.54/1.65  #Partial instantiations: 0
% 3.54/1.65  #Strategies tried      : 1
% 3.54/1.65  
% 3.54/1.65  Timing (in seconds)
% 3.54/1.65  ----------------------
% 3.54/1.65  Preprocessing        : 0.32
% 3.54/1.65  Parsing              : 0.16
% 3.54/1.65  CNF conversion       : 0.02
% 3.54/1.65  Main loop            : 0.49
% 3.54/1.65  Inferencing          : 0.19
% 3.54/1.65  Reduction            : 0.14
% 3.54/1.65  Demodulation         : 0.10
% 3.54/1.65  BG Simplification    : 0.02
% 3.54/1.65  Subsumption          : 0.10
% 3.54/1.65  Abstraction          : 0.02
% 3.54/1.65  MUC search           : 0.00
% 3.54/1.65  Cooper               : 0.00
% 3.54/1.65  Total                : 0.84
% 3.54/1.65  Index Insertion      : 0.00
% 3.54/1.65  Index Deletion       : 0.00
% 3.54/1.65  Index Matching       : 0.00
% 3.54/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
