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
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 110 expanded)
%              Number of leaves         :   38 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 203 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_65,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_91,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_111,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_115,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_193,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_196,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_193])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_115,c_196])).

tff(c_200,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_199])).

tff(c_18,plain,(
    ! [A_9,B_11] :
      ( k9_relat_1(A_9,k1_tarski(B_11)) = k11_relat_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_318,plain,(
    ! [A_84] :
      ( k9_relat_1(A_84,k1_relat_1('#skF_6')) = k11_relat_1(A_84,'#skF_3')
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_18])).

tff(c_22,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_325,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_22])).

tff(c_338,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_325])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_223,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_4])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(k1_funct_1(B_16,A_15)) = k11_relat_1(B_16,A_15)
      | ~ r2_hidden(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_232,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_223,c_24])).

tff(c_235,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_52,c_232])).

tff(c_134,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_137,plain,(
    ! [D_62] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_62) = k9_relat_1('#skF_6',D_62) ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_138,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_44])).

tff(c_283,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_138])).

tff(c_343,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_283])).

tff(c_358,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_343])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.37  
% 2.62/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.37  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.62/1.37  
% 2.62/1.37  %Foreground sorts:
% 2.62/1.37  
% 2.62/1.37  
% 2.62/1.37  %Background operators:
% 2.62/1.37  
% 2.62/1.37  
% 2.62/1.37  %Foreground operators:
% 2.62/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.37  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.37  
% 2.62/1.39  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.62/1.39  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.39  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.62/1.39  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.39  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.39  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.62/1.39  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.62/1.39  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.62/1.39  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.62/1.39  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.62/1.39  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.62/1.39  tff(c_91, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.39  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_91])).
% 2.62/1.39  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, A_12), k2_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.39  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.62/1.39  tff(c_50, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.62/1.39  tff(c_111, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.39  tff(c_115, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_111])).
% 2.62/1.39  tff(c_193, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.62/1.39  tff(c_196, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_48, c_193])).
% 2.62/1.39  tff(c_199, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_115, c_196])).
% 2.62/1.39  tff(c_200, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_199])).
% 2.62/1.39  tff(c_18, plain, (![A_9, B_11]: (k9_relat_1(A_9, k1_tarski(B_11))=k11_relat_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.39  tff(c_318, plain, (![A_84]: (k9_relat_1(A_84, k1_relat_1('#skF_6'))=k11_relat_1(A_84, '#skF_3') | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_200, c_18])).
% 2.62/1.39  tff(c_22, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.39  tff(c_325, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_318, c_22])).
% 2.62/1.39  tff(c_338, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_325])).
% 2.62/1.39  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.62/1.39  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.39  tff(c_223, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_4])).
% 2.62/1.39  tff(c_24, plain, (![B_16, A_15]: (k1_tarski(k1_funct_1(B_16, A_15))=k11_relat_1(B_16, A_15) | ~r2_hidden(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.39  tff(c_232, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_223, c_24])).
% 2.62/1.39  tff(c_235, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_52, c_232])).
% 2.62/1.39  tff(c_134, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.62/1.39  tff(c_137, plain, (![D_62]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_62)=k9_relat_1('#skF_6', D_62))), inference(resolution, [status(thm)], [c_48, c_134])).
% 2.62/1.39  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.62/1.39  tff(c_138, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_44])).
% 2.62/1.39  tff(c_283, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k11_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_138])).
% 2.62/1.39  tff(c_343, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_283])).
% 2.62/1.39  tff(c_358, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_343])).
% 2.62/1.39  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_358])).
% 2.62/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.39  
% 2.62/1.39  Inference rules
% 2.62/1.39  ----------------------
% 2.62/1.39  #Ref     : 0
% 2.62/1.39  #Sup     : 67
% 2.62/1.39  #Fact    : 0
% 2.62/1.39  #Define  : 0
% 2.62/1.39  #Split   : 0
% 2.62/1.39  #Chain   : 0
% 2.62/1.39  #Close   : 0
% 2.62/1.39  
% 2.62/1.39  Ordering : KBO
% 2.62/1.39  
% 2.62/1.39  Simplification rules
% 2.62/1.39  ----------------------
% 2.62/1.39  #Subsume      : 1
% 2.62/1.39  #Demod        : 47
% 2.62/1.39  #Tautology    : 38
% 2.62/1.39  #SimpNegUnit  : 4
% 2.62/1.39  #BackRed      : 9
% 2.62/1.39  
% 2.62/1.39  #Partial instantiations: 0
% 2.62/1.39  #Strategies tried      : 1
% 2.62/1.39  
% 2.62/1.39  Timing (in seconds)
% 2.62/1.39  ----------------------
% 2.62/1.39  Preprocessing        : 0.35
% 2.62/1.39  Parsing              : 0.19
% 2.62/1.39  CNF conversion       : 0.02
% 2.62/1.39  Main loop            : 0.24
% 2.62/1.39  Inferencing          : 0.09
% 2.62/1.39  Reduction            : 0.07
% 2.62/1.39  Demodulation         : 0.05
% 2.62/1.39  BG Simplification    : 0.02
% 2.62/1.39  Subsumption          : 0.05
% 2.62/1.39  Abstraction          : 0.01
% 2.62/1.39  MUC search           : 0.00
% 2.62/1.39  Cooper               : 0.00
% 2.62/1.39  Total                : 0.62
% 2.62/1.39  Index Insertion      : 0.00
% 2.62/1.39  Index Deletion       : 0.00
% 2.62/1.39  Index Matching       : 0.00
% 2.62/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
