%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   57 (  67 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 ( 113 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_69,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_121,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_121])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,(
    ! [B_75,C_76,A_77] :
      ( r2_hidden(k1_funct_1(B_75,C_76),A_77)
      | ~ r2_hidden(C_76,k1_relat_1(B_75))
      | ~ v1_funct_1(B_75)
      | ~ v5_relat_1(B_75,A_77)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_217,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_40])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_125,c_48,c_217])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_169,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_173,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_169])).

tff(c_222,plain,(
    ! [B_78,A_79,C_80] :
      ( k1_xboole_0 = B_78
      | k1_relset_1(A_79,B_78,C_80) = A_79
      | ~ v1_funct_2(C_80,A_79,B_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_225,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_222])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_173,c_225])).

tff(c_229,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_228])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(A_34,C_35)
      | ~ r1_tarski(k2_tarski(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_37,B_38] : r2_hidden(A_37,k2_tarski(A_37,B_38)) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_93,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_255,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_93])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.27  
% 2.35/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.27  
% 2.35/1.27  %Foreground sorts:
% 2.35/1.27  
% 2.35/1.27  
% 2.35/1.27  %Background operators:
% 2.35/1.27  
% 2.35/1.27  
% 2.35/1.27  %Foreground operators:
% 2.35/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.35/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.35/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.27  
% 2.35/1.28  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.35/1.28  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.35/1.28  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.35/1.28  tff(f_52, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.35/1.28  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.28  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.35/1.28  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.35/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.28  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.35/1.28  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.35/1.28  tff(c_69, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.28  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_69])).
% 2.35/1.28  tff(c_121, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.28  tff(c_125, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_121])).
% 2.35/1.28  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.35/1.28  tff(c_211, plain, (![B_75, C_76, A_77]: (r2_hidden(k1_funct_1(B_75, C_76), A_77) | ~r2_hidden(C_76, k1_relat_1(B_75)) | ~v1_funct_1(B_75) | ~v5_relat_1(B_75, A_77) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.35/1.28  tff(c_40, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.35/1.28  tff(c_217, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_40])).
% 2.35/1.28  tff(c_221, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_125, c_48, c_217])).
% 2.35/1.28  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.35/1.28  tff(c_46, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.35/1.28  tff(c_169, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.35/1.28  tff(c_173, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_169])).
% 2.35/1.28  tff(c_222, plain, (![B_78, A_79, C_80]: (k1_xboole_0=B_78 | k1_relset_1(A_79, B_78, C_80)=A_79 | ~v1_funct_2(C_80, A_79, B_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.35/1.28  tff(c_225, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_222])).
% 2.35/1.28  tff(c_228, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_173, c_225])).
% 2.35/1.28  tff(c_229, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_228])).
% 2.35/1.28  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.28  tff(c_81, plain, (![A_34, C_35, B_36]: (r2_hidden(A_34, C_35) | ~r1_tarski(k2_tarski(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.28  tff(c_90, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.35/1.28  tff(c_93, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 2.35/1.28  tff(c_255, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_93])).
% 2.35/1.28  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_255])).
% 2.35/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.28  
% 2.35/1.28  Inference rules
% 2.35/1.28  ----------------------
% 2.35/1.28  #Ref     : 0
% 2.35/1.28  #Sup     : 43
% 2.35/1.28  #Fact    : 0
% 2.35/1.28  #Define  : 0
% 2.35/1.28  #Split   : 0
% 2.35/1.28  #Chain   : 0
% 2.35/1.28  #Close   : 0
% 2.35/1.28  
% 2.35/1.28  Ordering : KBO
% 2.35/1.28  
% 2.35/1.28  Simplification rules
% 2.35/1.28  ----------------------
% 2.35/1.28  #Subsume      : 2
% 2.35/1.28  #Demod        : 22
% 2.35/1.28  #Tautology    : 18
% 2.35/1.28  #SimpNegUnit  : 3
% 2.35/1.28  #BackRed      : 4
% 2.35/1.28  
% 2.35/1.28  #Partial instantiations: 0
% 2.35/1.28  #Strategies tried      : 1
% 2.35/1.28  
% 2.35/1.28  Timing (in seconds)
% 2.35/1.28  ----------------------
% 2.35/1.29  Preprocessing        : 0.32
% 2.35/1.29  Parsing              : 0.17
% 2.35/1.29  CNF conversion       : 0.02
% 2.35/1.29  Main loop            : 0.20
% 2.35/1.29  Inferencing          : 0.07
% 2.35/1.29  Reduction            : 0.07
% 2.35/1.29  Demodulation         : 0.05
% 2.35/1.29  BG Simplification    : 0.01
% 2.35/1.29  Subsumption          : 0.04
% 2.35/1.29  Abstraction          : 0.01
% 2.35/1.29  MUC search           : 0.00
% 2.35/1.29  Cooper               : 0.00
% 2.35/1.29  Total                : 0.55
% 2.35/1.29  Index Insertion      : 0.00
% 2.35/1.29  Index Deletion       : 0.00
% 2.35/1.29  Index Matching       : 0.00
% 2.35/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
