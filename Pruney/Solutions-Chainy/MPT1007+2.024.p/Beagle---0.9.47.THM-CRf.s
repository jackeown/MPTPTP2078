%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 109 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_78,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_88,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_88])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_127,plain,(
    ! [B_54,C_55,A_56] :
      ( r2_hidden(k1_funct_1(B_54,C_55),A_56)
      | ~ r2_hidden(C_55,k1_relat_1(B_54))
      | ~ v1_funct_1(B_54)
      | ~ v5_relat_1(B_54,A_56)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_133,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_36])).

tff(c_137,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_92,c_44,c_133])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_107,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_138,plain,(
    ! [B_57,A_58,C_59] :
      ( k1_xboole_0 = B_57
      | k1_relset_1(A_58,B_57,C_59) = A_58
      | ~ v1_funct_2(C_59,A_58,B_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_141,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_138])).

tff(c_144,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_111,c_141])).

tff(c_145,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_144])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | ~ r1_tarski(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_24] : r2_hidden(A_24,k1_tarski(A_24)) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_161,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_61])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.23  
% 2.05/1.23  %Foreground sorts:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Background operators:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Foreground operators:
% 2.05/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.05/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.05/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.23  
% 2.10/1.24  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.10/1.24  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.10/1.24  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.10/1.24  tff(f_48, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.10/1.24  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.10/1.24  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.10/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.24  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.10/1.24  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.10/1.24  tff(c_78, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.24  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.10/1.24  tff(c_88, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.24  tff(c_92, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_88])).
% 2.10/1.24  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.10/1.24  tff(c_127, plain, (![B_54, C_55, A_56]: (r2_hidden(k1_funct_1(B_54, C_55), A_56) | ~r2_hidden(C_55, k1_relat_1(B_54)) | ~v1_funct_1(B_54) | ~v5_relat_1(B_54, A_56) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.24  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.10/1.24  tff(c_133, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_36])).
% 2.10/1.24  tff(c_137, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_92, c_44, c_133])).
% 2.10/1.24  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.10/1.24  tff(c_42, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.10/1.24  tff(c_107, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.24  tff(c_111, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.10/1.24  tff(c_138, plain, (![B_57, A_58, C_59]: (k1_xboole_0=B_57 | k1_relset_1(A_58, B_57, C_59)=A_58 | ~v1_funct_2(C_59, A_58, B_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.10/1.24  tff(c_141, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_40, c_138])).
% 2.10/1.24  tff(c_144, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_111, c_141])).
% 2.10/1.24  tff(c_145, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_144])).
% 2.10/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.24  tff(c_56, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | ~r1_tarski(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.24  tff(c_61, plain, (![A_24]: (r2_hidden(A_24, k1_tarski(A_24)))), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.10/1.24  tff(c_161, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_61])).
% 2.10/1.24  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_161])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 25
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 0
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 0
% 2.10/1.24  #Demod        : 15
% 2.10/1.24  #Tautology    : 10
% 2.10/1.24  #SimpNegUnit  : 2
% 2.10/1.24  #BackRed      : 4
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.25  Preprocessing        : 0.33
% 2.10/1.25  Parsing              : 0.17
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.16
% 2.10/1.25  Inferencing          : 0.05
% 2.10/1.25  Reduction            : 0.05
% 2.10/1.25  Demodulation         : 0.04
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.03
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.51
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.25  Index Matching       : 0.00
% 2.10/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
