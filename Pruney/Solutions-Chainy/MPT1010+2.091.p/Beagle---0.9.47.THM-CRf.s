%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   74 (  98 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 183 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_76,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_194,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_197,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_78,c_194])).

tff(c_200,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_197])).

tff(c_82,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_80,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_232,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_236,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_232])).

tff(c_930,plain,(
    ! [B_178,A_179,C_180] :
      ( k1_xboole_0 = B_178
      | k1_relset_1(A_179,B_178,C_180) = A_179
      | ~ v1_funct_2(C_180,A_179,B_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_933,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_930])).

tff(c_936,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_236,c_933])).

tff(c_937,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_936])).

tff(c_201,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_205,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_201])).

tff(c_799,plain,(
    ! [B_155,A_156] :
      ( r2_hidden(k1_funct_1(B_155,A_156),k2_relat_1(B_155))
      | ~ r2_hidden(A_156,k1_relat_1(B_155))
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [C_28,A_25,B_26] :
      ( r2_hidden(C_28,A_25)
      | ~ r2_hidden(C_28,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_889,plain,(
    ! [B_170,A_171,A_172] :
      ( r2_hidden(k1_funct_1(B_170,A_171),A_172)
      | ~ v5_relat_1(B_170,A_172)
      | ~ r2_hidden(A_171,k1_relat_1(B_170))
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_799,c_52])).

tff(c_32,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_953,plain,(
    ! [B_183,A_184,A_185] :
      ( k1_funct_1(B_183,A_184) = A_185
      | ~ v5_relat_1(B_183,k1_tarski(A_185))
      | ~ r2_hidden(A_184,k1_relat_1(B_183))
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_889,c_32])).

tff(c_955,plain,(
    ! [A_184] :
      ( k1_funct_1('#skF_9',A_184) = '#skF_7'
      | ~ r2_hidden(A_184,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_205,c_953])).

tff(c_960,plain,(
    ! [A_190] :
      ( k1_funct_1('#skF_9',A_190) = '#skF_7'
      | ~ r2_hidden(A_190,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_82,c_937,c_955])).

tff(c_983,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_76,c_960])).

tff(c_994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_983])).

tff(c_995,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_936])).

tff(c_34,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [C_16] : ~ v1_xboole_0(k1_tarski(C_16)) ),
    inference(resolution,[status(thm)],[c_34,c_85])).

tff(c_1021,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_92])).

tff(c_1032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  
% 3.30/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.30/1.51  
% 3.30/1.51  %Foreground sorts:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Background operators:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Foreground operators:
% 3.30/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.30/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.30/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.30/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.30/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.30/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.30/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.30/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.30/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.30/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.30/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.51  
% 3.45/1.52  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.45/1.52  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.45/1.52  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.45/1.52  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.45/1.52  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.45/1.52  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.45/1.52  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.45/1.52  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.45/1.52  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 3.45/1.52  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.45/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.45/1.52  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.52  tff(c_74, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.45/1.52  tff(c_76, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.45/1.52  tff(c_50, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.45/1.52  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.45/1.52  tff(c_194, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.45/1.52  tff(c_197, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_78, c_194])).
% 3.45/1.52  tff(c_200, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_197])).
% 3.45/1.52  tff(c_82, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.45/1.52  tff(c_80, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.45/1.52  tff(c_232, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.45/1.52  tff(c_236, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_232])).
% 3.45/1.52  tff(c_930, plain, (![B_178, A_179, C_180]: (k1_xboole_0=B_178 | k1_relset_1(A_179, B_178, C_180)=A_179 | ~v1_funct_2(C_180, A_179, B_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.45/1.52  tff(c_933, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_930])).
% 3.45/1.52  tff(c_936, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_236, c_933])).
% 3.45/1.52  tff(c_937, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_936])).
% 3.45/1.52  tff(c_201, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.45/1.52  tff(c_205, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_201])).
% 3.45/1.52  tff(c_799, plain, (![B_155, A_156]: (r2_hidden(k1_funct_1(B_155, A_156), k2_relat_1(B_155)) | ~r2_hidden(A_156, k1_relat_1(B_155)) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.45/1.52  tff(c_52, plain, (![C_28, A_25, B_26]: (r2_hidden(C_28, A_25) | ~r2_hidden(C_28, k2_relat_1(B_26)) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.45/1.52  tff(c_889, plain, (![B_170, A_171, A_172]: (r2_hidden(k1_funct_1(B_170, A_171), A_172) | ~v5_relat_1(B_170, A_172) | ~r2_hidden(A_171, k1_relat_1(B_170)) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_799, c_52])).
% 3.45/1.52  tff(c_32, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.45/1.52  tff(c_953, plain, (![B_183, A_184, A_185]: (k1_funct_1(B_183, A_184)=A_185 | ~v5_relat_1(B_183, k1_tarski(A_185)) | ~r2_hidden(A_184, k1_relat_1(B_183)) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_889, c_32])).
% 3.45/1.52  tff(c_955, plain, (![A_184]: (k1_funct_1('#skF_9', A_184)='#skF_7' | ~r2_hidden(A_184, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_205, c_953])).
% 3.45/1.52  tff(c_960, plain, (![A_190]: (k1_funct_1('#skF_9', A_190)='#skF_7' | ~r2_hidden(A_190, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_82, c_937, c_955])).
% 3.45/1.52  tff(c_983, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_76, c_960])).
% 3.45/1.52  tff(c_994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_983])).
% 3.45/1.52  tff(c_995, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_936])).
% 3.45/1.52  tff(c_34, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.45/1.52  tff(c_85, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.52  tff(c_92, plain, (![C_16]: (~v1_xboole_0(k1_tarski(C_16)))), inference(resolution, [status(thm)], [c_34, c_85])).
% 3.45/1.52  tff(c_1021, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_995, c_92])).
% 3.45/1.52  tff(c_1032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1021])).
% 3.45/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.52  
% 3.45/1.52  Inference rules
% 3.45/1.52  ----------------------
% 3.45/1.52  #Ref     : 0
% 3.45/1.52  #Sup     : 195
% 3.45/1.52  #Fact    : 2
% 3.45/1.52  #Define  : 0
% 3.45/1.52  #Split   : 4
% 3.45/1.52  #Chain   : 0
% 3.45/1.52  #Close   : 0
% 3.45/1.52  
% 3.45/1.52  Ordering : KBO
% 3.45/1.52  
% 3.45/1.52  Simplification rules
% 3.45/1.52  ----------------------
% 3.45/1.52  #Subsume      : 22
% 3.45/1.52  #Demod        : 109
% 3.45/1.52  #Tautology    : 74
% 3.45/1.52  #SimpNegUnit  : 11
% 3.45/1.52  #BackRed      : 15
% 3.45/1.52  
% 3.45/1.52  #Partial instantiations: 0
% 3.45/1.52  #Strategies tried      : 1
% 3.45/1.52  
% 3.45/1.52  Timing (in seconds)
% 3.45/1.52  ----------------------
% 3.45/1.53  Preprocessing        : 0.36
% 3.45/1.53  Parsing              : 0.18
% 3.45/1.53  CNF conversion       : 0.03
% 3.45/1.53  Main loop            : 0.43
% 3.45/1.53  Inferencing          : 0.15
% 3.45/1.53  Reduction            : 0.13
% 3.45/1.53  Demodulation         : 0.09
% 3.45/1.53  BG Simplification    : 0.03
% 3.45/1.53  Subsumption          : 0.08
% 3.45/1.53  Abstraction          : 0.03
% 3.45/1.53  MUC search           : 0.00
% 3.45/1.53  Cooper               : 0.00
% 3.52/1.53  Total                : 0.82
% 3.52/1.53  Index Insertion      : 0.00
% 3.52/1.53  Index Deletion       : 0.00
% 3.52/1.53  Index Matching       : 0.00
% 3.52/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
