%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:06 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   60 (  73 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 146 expanded)
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

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_66,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_72])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_132,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_132])).

tff(c_443,plain,(
    ! [B_113,A_114,C_115] :
      ( k1_xboole_0 = B_113
      | k1_relset_1(A_114,B_113,C_115) = A_114
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_454,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_443])).

tff(c_459,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_141,c_454])).

tff(c_460,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_459])).

tff(c_122,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_131,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_161,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1(k2_relset_1(A_62,B_63,C_64),k1_zfmisc_1(B_63))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_161])).

tff(c_184,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_178])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_192,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_8])).

tff(c_225,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(k1_funct_1(B_69,A_70),k2_relat_1(B_69))
      | ~ r2_hidden(A_70,k1_relat_1(B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_991,plain,(
    ! [B_175,A_176,B_177] :
      ( r2_hidden(k1_funct_1(B_175,A_176),B_177)
      | ~ r1_tarski(k2_relat_1(B_175),B_177)
      | ~ r2_hidden(A_176,k1_relat_1(B_175))
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175) ) ),
    inference(resolution,[status(thm)],[c_225,c_2])).

tff(c_36,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_996,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_991,c_36])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_40,c_460,c_192,c_996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.13  
% 4.24/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.13  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.24/2.13  
% 4.24/2.13  %Foreground sorts:
% 4.24/2.13  
% 4.24/2.13  
% 4.24/2.13  %Background operators:
% 4.24/2.13  
% 4.24/2.13  
% 4.24/2.13  %Foreground operators:
% 4.24/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.24/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.24/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.24/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.24/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.24/2.13  tff('#skF_5', type, '#skF_5': $i).
% 4.24/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.24/2.13  tff('#skF_2', type, '#skF_2': $i).
% 4.24/2.13  tff('#skF_3', type, '#skF_3': $i).
% 4.24/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.24/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.24/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.24/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.24/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.24/2.13  tff('#skF_4', type, '#skF_4': $i).
% 4.24/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.24/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.24/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.24/2.13  
% 4.24/2.15  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.24/2.15  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.24/2.15  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.24/2.15  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.24/2.15  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.24/2.15  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.24/2.15  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.24/2.15  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.24/2.15  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.24/2.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.24/2.15  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.24/2.15  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/2.15  tff(c_66, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.24/2.15  tff(c_72, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_66])).
% 4.24/2.15  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_72])).
% 4.24/2.15  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/2.15  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/2.15  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/2.15  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/2.15  tff(c_132, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.24/2.15  tff(c_141, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_132])).
% 4.24/2.15  tff(c_443, plain, (![B_113, A_114, C_115]: (k1_xboole_0=B_113 | k1_relset_1(A_114, B_113, C_115)=A_114 | ~v1_funct_2(C_115, A_114, B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/2.15  tff(c_454, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_443])).
% 4.24/2.15  tff(c_459, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_141, c_454])).
% 4.24/2.15  tff(c_460, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_459])).
% 4.24/2.15  tff(c_122, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.24/2.15  tff(c_131, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_122])).
% 4.24/2.15  tff(c_161, plain, (![A_62, B_63, C_64]: (m1_subset_1(k2_relset_1(A_62, B_63, C_64), k1_zfmisc_1(B_63)) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.24/2.15  tff(c_178, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_161])).
% 4.24/2.15  tff(c_184, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_178])).
% 4.24/2.15  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/2.15  tff(c_192, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_184, c_8])).
% 4.24/2.15  tff(c_225, plain, (![B_69, A_70]: (r2_hidden(k1_funct_1(B_69, A_70), k2_relat_1(B_69)) | ~r2_hidden(A_70, k1_relat_1(B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.24/2.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.24/2.15  tff(c_991, plain, (![B_175, A_176, B_177]: (r2_hidden(k1_funct_1(B_175, A_176), B_177) | ~r1_tarski(k2_relat_1(B_175), B_177) | ~r2_hidden(A_176, k1_relat_1(B_175)) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175))), inference(resolution, [status(thm)], [c_225, c_2])).
% 4.24/2.15  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.24/2.15  tff(c_996, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~r2_hidden('#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_991, c_36])).
% 4.24/2.15  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_40, c_460, c_192, c_996])).
% 4.24/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.15  
% 4.24/2.15  Inference rules
% 4.24/2.15  ----------------------
% 4.24/2.15  #Ref     : 0
% 4.24/2.15  #Sup     : 195
% 4.24/2.15  #Fact    : 0
% 4.24/2.15  #Define  : 0
% 4.24/2.15  #Split   : 5
% 4.24/2.15  #Chain   : 0
% 4.24/2.15  #Close   : 0
% 4.24/2.15  
% 4.24/2.15  Ordering : KBO
% 4.24/2.15  
% 4.24/2.15  Simplification rules
% 4.24/2.15  ----------------------
% 4.24/2.15  #Subsume      : 19
% 4.24/2.15  #Demod        : 53
% 4.24/2.15  #Tautology    : 47
% 4.24/2.15  #SimpNegUnit  : 8
% 4.24/2.15  #BackRed      : 1
% 4.24/2.15  
% 4.24/2.15  #Partial instantiations: 0
% 4.24/2.16  #Strategies tried      : 1
% 4.24/2.16  
% 4.24/2.16  Timing (in seconds)
% 4.24/2.16  ----------------------
% 4.24/2.16  Preprocessing        : 0.51
% 4.24/2.16  Parsing              : 0.26
% 4.24/2.16  CNF conversion       : 0.04
% 4.24/2.16  Main loop            : 0.71
% 4.24/2.16  Inferencing          : 0.28
% 4.24/2.16  Reduction            : 0.21
% 4.24/2.16  Demodulation         : 0.14
% 4.24/2.16  BG Simplification    : 0.04
% 4.24/2.16  Subsumption          : 0.14
% 4.24/2.16  Abstraction          : 0.03
% 4.24/2.16  MUC search           : 0.00
% 4.24/2.16  Cooper               : 0.00
% 4.24/2.16  Total                : 1.28
% 4.24/2.16  Index Insertion      : 0.00
% 4.24/2.16  Index Deletion       : 0.00
% 4.24/2.16  Index Matching       : 0.00
% 4.24/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
