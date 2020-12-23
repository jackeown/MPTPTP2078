%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:16 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  68 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 112 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_102,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_112,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_112])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_169,plain,(
    ! [B_72,C_73,A_74] :
      ( r2_hidden(k1_funct_1(B_72,C_73),A_74)
      | ~ r2_hidden(C_73,k1_relat_1(B_72))
      | ~ v1_funct_1(B_72)
      | ~ v5_relat_1(B_72,A_74)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_184,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_52])).

tff(c_190,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_116,c_60,c_184])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_157,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_203,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_206,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_203])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_161,c_206])).

tff(c_210,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_209])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_73,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_39,B_40] : r2_hidden(A_39,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6])).

tff(c_94,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_221,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_94])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.21/1.34  
% 2.21/1.34  %Foreground sorts:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Background operators:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Foreground operators:
% 2.21/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.21/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.21/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.21/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.34  
% 2.21/1.35  tff(f_99, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.21/1.35  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.35  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.21/1.35  tff(f_55, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.21/1.35  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.35  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.21/1.35  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.35  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.35  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.21/1.35  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.21/1.35  tff(c_102, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.21/1.35  tff(c_106, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_102])).
% 2.21/1.35  tff(c_112, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.35  tff(c_116, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_112])).
% 2.21/1.35  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.21/1.35  tff(c_169, plain, (![B_72, C_73, A_74]: (r2_hidden(k1_funct_1(B_72, C_73), A_74) | ~r2_hidden(C_73, k1_relat_1(B_72)) | ~v1_funct_1(B_72) | ~v5_relat_1(B_72, A_74) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.35  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.21/1.35  tff(c_184, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_52])).
% 2.21/1.35  tff(c_190, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_116, c_60, c_184])).
% 2.21/1.35  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.21/1.35  tff(c_58, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.21/1.35  tff(c_157, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.35  tff(c_161, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_157])).
% 2.21/1.35  tff(c_203, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.21/1.35  tff(c_206, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_56, c_203])).
% 2.21/1.35  tff(c_209, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_161, c_206])).
% 2.21/1.35  tff(c_210, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_209])).
% 2.21/1.35  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.35  tff(c_73, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.35  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.35  tff(c_91, plain, (![A_39, B_40]: (r2_hidden(A_39, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6])).
% 2.21/1.35  tff(c_94, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_91])).
% 2.21/1.35  tff(c_221, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_94])).
% 2.21/1.35  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_221])).
% 2.21/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  Inference rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Ref     : 0
% 2.21/1.35  #Sup     : 34
% 2.21/1.35  #Fact    : 0
% 2.21/1.35  #Define  : 0
% 2.21/1.35  #Split   : 0
% 2.21/1.35  #Chain   : 0
% 2.21/1.35  #Close   : 0
% 2.21/1.35  
% 2.21/1.35  Ordering : KBO
% 2.21/1.35  
% 2.21/1.35  Simplification rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Subsume      : 0
% 2.21/1.35  #Demod        : 13
% 2.21/1.35  #Tautology    : 16
% 2.21/1.35  #SimpNegUnit  : 3
% 2.21/1.35  #BackRed      : 4
% 2.21/1.35  
% 2.21/1.35  #Partial instantiations: 0
% 2.21/1.35  #Strategies tried      : 1
% 2.21/1.35  
% 2.21/1.35  Timing (in seconds)
% 2.21/1.35  ----------------------
% 2.21/1.35  Preprocessing        : 0.34
% 2.21/1.35  Parsing              : 0.18
% 2.21/1.35  CNF conversion       : 0.02
% 2.21/1.35  Main loop            : 0.19
% 2.21/1.35  Inferencing          : 0.06
% 2.21/1.35  Reduction            : 0.06
% 2.21/1.36  Demodulation         : 0.04
% 2.21/1.36  BG Simplification    : 0.02
% 2.21/1.36  Subsumption          : 0.04
% 2.21/1.36  Abstraction          : 0.01
% 2.21/1.36  MUC search           : 0.00
% 2.21/1.36  Cooper               : 0.00
% 2.21/1.36  Total                : 0.55
% 2.21/1.36  Index Insertion      : 0.00
% 2.21/1.36  Index Deletion       : 0.00
% 2.21/1.36  Index Matching       : 0.00
% 2.21/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
