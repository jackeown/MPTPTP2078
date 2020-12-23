%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:36 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 176 expanded)
%              Number of equality atoms :   37 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_126,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_44,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_127,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_44])).

tff(c_87,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_113,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_117,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_171,plain,(
    ! [B_69,A_70,C_71] :
      ( k1_xboole_0 = B_69
      | k1_relset_1(A_70,B_69,C_71) = A_70
      | ~ v1_funct_2(C_71,A_70,B_69)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_171])).

tff(c_177,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_117,c_174])).

tff(c_178,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_177])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_198,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_4])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_280,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(k7_relat_1(B_78,k1_tarski(A_79))) = k1_tarski(k1_funct_1(B_78,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(B_78))
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_315,plain,(
    ! [B_81,A_82] :
      ( k9_relat_1(B_81,k1_tarski(A_82)) = k1_tarski(k1_funct_1(B_81,A_82))
      | ~ r2_hidden(A_82,k1_relat_1(B_81))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_280])).

tff(c_318,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k1_tarski(k1_funct_1('#skF_5','#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_198,c_315])).

tff(c_329,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_52,c_178,c_318])).

tff(c_20,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_342,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_20])).

tff(c_349,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_342])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.36/1.35  
% 2.36/1.35  %Foreground sorts:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Background operators:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Foreground operators:
% 2.36/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.36/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.36/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.35  
% 2.36/1.37  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.36/1.37  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.36/1.37  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.36/1.37  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.36/1.37  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.36/1.37  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.36/1.37  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.36/1.37  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 2.36/1.37  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.36/1.37  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.37  tff(c_122, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.37  tff(c_126, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_122])).
% 2.36/1.37  tff(c_44, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.37  tff(c_127, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_44])).
% 2.36/1.37  tff(c_87, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.37  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_87])).
% 2.36/1.37  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.37  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.37  tff(c_50, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.37  tff(c_113, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.37  tff(c_117, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_113])).
% 2.36/1.37  tff(c_171, plain, (![B_69, A_70, C_71]: (k1_xboole_0=B_69 | k1_relset_1(A_70, B_69, C_71)=A_70 | ~v1_funct_2(C_71, A_70, B_69) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.36/1.37  tff(c_174, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_48, c_171])).
% 2.36/1.37  tff(c_177, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_117, c_174])).
% 2.36/1.37  tff(c_178, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_177])).
% 2.36/1.37  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.37  tff(c_198, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_4])).
% 2.36/1.37  tff(c_22, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.37  tff(c_280, plain, (![B_78, A_79]: (k2_relat_1(k7_relat_1(B_78, k1_tarski(A_79)))=k1_tarski(k1_funct_1(B_78, A_79)) | ~r2_hidden(A_79, k1_relat_1(B_78)) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.37  tff(c_315, plain, (![B_81, A_82]: (k9_relat_1(B_81, k1_tarski(A_82))=k1_tarski(k1_funct_1(B_81, A_82)) | ~r2_hidden(A_82, k1_relat_1(B_81)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_22, c_280])).
% 2.36/1.37  tff(c_318, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k1_tarski(k1_funct_1('#skF_5', '#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_198, c_315])).
% 2.36/1.37  tff(c_329, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_52, c_178, c_318])).
% 2.36/1.37  tff(c_20, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.37  tff(c_342, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_329, c_20])).
% 2.36/1.37  tff(c_349, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_342])).
% 2.36/1.37  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_349])).
% 2.36/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  Inference rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Ref     : 0
% 2.36/1.37  #Sup     : 67
% 2.36/1.37  #Fact    : 0
% 2.36/1.37  #Define  : 0
% 2.36/1.37  #Split   : 0
% 2.36/1.37  #Chain   : 0
% 2.36/1.37  #Close   : 0
% 2.36/1.37  
% 2.36/1.37  Ordering : KBO
% 2.36/1.37  
% 2.36/1.37  Simplification rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Subsume      : 3
% 2.36/1.37  #Demod        : 31
% 2.36/1.37  #Tautology    : 41
% 2.36/1.37  #SimpNegUnit  : 4
% 2.36/1.37  #BackRed      : 5
% 2.36/1.37  
% 2.36/1.37  #Partial instantiations: 0
% 2.36/1.37  #Strategies tried      : 1
% 2.36/1.37  
% 2.36/1.37  Timing (in seconds)
% 2.36/1.37  ----------------------
% 2.36/1.37  Preprocessing        : 0.32
% 2.36/1.37  Parsing              : 0.17
% 2.36/1.37  CNF conversion       : 0.02
% 2.36/1.37  Main loop            : 0.24
% 2.36/1.37  Inferencing          : 0.09
% 2.36/1.37  Reduction            : 0.07
% 2.36/1.37  Demodulation         : 0.05
% 2.36/1.37  BG Simplification    : 0.02
% 2.36/1.37  Subsumption          : 0.05
% 2.36/1.37  Abstraction          : 0.01
% 2.36/1.37  MUC search           : 0.00
% 2.36/1.37  Cooper               : 0.00
% 2.36/1.37  Total                : 0.60
% 2.36/1.37  Index Insertion      : 0.00
% 2.36/1.37  Index Deletion       : 0.00
% 2.36/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
