%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 119 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 260 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50])).

tff(c_114,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_114])).

tff(c_119,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_137,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k2_relat_1(B_55),A_56)
      | ~ v5_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_2'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_35,B_36] :
      ( ~ v1_xboole_0(A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [B_36,A_35] :
      ( B_36 = A_35
      | ~ r1_tarski(B_36,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_83,c_14])).

tff(c_198,plain,(
    ! [B_71,A_72] :
      ( k2_relat_1(B_71) = A_72
      | ~ v1_xboole_0(A_72)
      | ~ v5_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_137,c_86])).

tff(c_204,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_198])).

tff(c_209,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_204])).

tff(c_210,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_52,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_407,plain,(
    ! [B_110,C_111,A_112] :
      ( k1_xboole_0 = B_110
      | v1_funct_2(C_111,A_112,B_110)
      | k1_relset_1(A_112,B_110,C_111) != A_112
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_416,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_407])).

tff(c_423,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_416])).

tff(c_424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_423])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_431,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_12])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_431])).

tff(c_434,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_183,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_186,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_183])).

tff(c_188,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_186])).

tff(c_46,plain,(
    ! [A_26] :
      ( v1_funct_2(A_26,k1_relat_1(A_26),k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_192,plain,
    ( v1_funct_2('#skF_5','#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_46])).

tff(c_196,plain,(
    v1_funct_2('#skF_5','#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_56,c_192])).

tff(c_450,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_196])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:46:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.69/1.37  
% 2.69/1.37  %Foreground sorts:
% 2.69/1.37  
% 2.69/1.37  
% 2.69/1.37  %Background operators:
% 2.69/1.37  
% 2.69/1.37  
% 2.69/1.37  %Foreground operators:
% 2.69/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.69/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.37  
% 2.69/1.39  tff(f_106, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.69/1.39  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.39  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.39  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.69/1.39  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.69/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.69/1.39  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.39  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.69/1.39  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.39  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.69/1.39  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 2.69/1.39  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.69/1.39  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.69/1.39  tff(c_50, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.69/1.39  tff(c_58, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50])).
% 2.69/1.39  tff(c_114, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.39  tff(c_118, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_114])).
% 2.69/1.39  tff(c_119, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.39  tff(c_123, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_119])).
% 2.69/1.39  tff(c_137, plain, (![B_55, A_56]: (r1_tarski(k2_relat_1(B_55), A_56) | ~v5_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.39  tff(c_71, plain, (![A_31, B_32]: (r2_hidden('#skF_2'(A_31, B_32), A_31) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.39  tff(c_83, plain, (![A_35, B_36]: (~v1_xboole_0(A_35) | r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.69/1.39  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.39  tff(c_86, plain, (![B_36, A_35]: (B_36=A_35 | ~r1_tarski(B_36, A_35) | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_83, c_14])).
% 2.69/1.39  tff(c_198, plain, (![B_71, A_72]: (k2_relat_1(B_71)=A_72 | ~v1_xboole_0(A_72) | ~v5_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_137, c_86])).
% 2.69/1.39  tff(c_204, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_123, c_198])).
% 2.69/1.39  tff(c_209, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_204])).
% 2.69/1.39  tff(c_210, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 2.69/1.39  tff(c_52, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.69/1.39  tff(c_407, plain, (![B_110, C_111, A_112]: (k1_xboole_0=B_110 | v1_funct_2(C_111, A_112, B_110) | k1_relset_1(A_112, B_110, C_111)!=A_112 | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.69/1.39  tff(c_416, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_54, c_407])).
% 2.69/1.39  tff(c_423, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_416])).
% 2.69/1.39  tff(c_424, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_423])).
% 2.69/1.39  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.39  tff(c_431, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_12])).
% 2.69/1.39  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_431])).
% 2.69/1.39  tff(c_434, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_209])).
% 2.69/1.39  tff(c_183, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.39  tff(c_186, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_183])).
% 2.69/1.39  tff(c_188, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_186])).
% 2.69/1.39  tff(c_46, plain, (![A_26]: (v1_funct_2(A_26, k1_relat_1(A_26), k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.69/1.39  tff(c_192, plain, (v1_funct_2('#skF_5', '#skF_3', k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_188, c_46])).
% 2.69/1.39  tff(c_196, plain, (v1_funct_2('#skF_5', '#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_56, c_192])).
% 2.69/1.39  tff(c_450, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_196])).
% 2.69/1.39  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_450])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 83
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 1
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 14
% 2.69/1.39  #Demod        : 55
% 2.69/1.39  #Tautology    : 36
% 2.69/1.39  #SimpNegUnit  : 3
% 2.69/1.39  #BackRed      : 10
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.39  Preprocessing        : 0.34
% 2.69/1.39  Parsing              : 0.17
% 2.69/1.39  CNF conversion       : 0.02
% 2.69/1.39  Main loop            : 0.29
% 2.69/1.39  Inferencing          : 0.10
% 2.69/1.39  Reduction            : 0.08
% 2.69/1.39  Demodulation         : 0.06
% 2.69/1.39  BG Simplification    : 0.02
% 2.69/1.40  Subsumption          : 0.06
% 2.69/1.40  Abstraction          : 0.02
% 2.69/1.40  MUC search           : 0.00
% 2.69/1.40  Cooper               : 0.00
% 2.69/1.40  Total                : 0.67
% 2.69/1.40  Index Insertion      : 0.00
% 2.69/1.40  Index Deletion       : 0.00
% 2.69/1.40  Index Matching       : 0.00
% 2.69/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
