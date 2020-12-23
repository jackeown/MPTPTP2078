%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   36 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_85,axiom,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_18,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_66,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_63])).

tff(c_54,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_91,plain,(
    ! [B_67,A_68] :
      ( k1_funct_1(k2_funct_1(B_67),k1_funct_1(B_67,A_68)) = A_68
      | ~ r2_hidden(A_68,k1_relat_1(B_67))
      | ~ v2_funct_1(B_67)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10','#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_100,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_42])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_48,c_100])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,(
    ! [B_64,A_65,C_66] :
      ( k1_xboole_0 = B_64
      | k1_relset_1(A_65,B_64,C_66) = A_65
      | ~ v1_funct_2(C_66,A_65,B_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_85,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_86,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_85])).

tff(c_46,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_174,plain,(
    ! [D_95,A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski(D_95,'#skF_6'(A_96,B_97,C_98,D_95)),C_98)
      | ~ r2_hidden(D_95,B_97)
      | k1_relset_1(B_97,A_96,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(B_97,A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k1_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(C_19,D_22),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [D_99,C_100,B_101,A_102] :
      ( r2_hidden(D_99,k1_relat_1(C_100))
      | ~ r2_hidden(D_99,B_101)
      | k1_relset_1(B_101,A_102,C_100) != B_101
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(B_101,A_102))) ) ),
    inference(resolution,[status(thm)],[c_174,c_8])).

tff(c_220,plain,(
    ! [C_107,A_108] :
      ( r2_hidden('#skF_9',k1_relat_1(C_107))
      | k1_relset_1('#skF_7',A_108,C_107) != '#skF_7'
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_7',A_108))) ) ),
    inference(resolution,[status(thm)],[c_46,c_188])).

tff(c_223,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | k1_relset_1('#skF_7','#skF_8','#skF_10') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_50,c_220])).

tff(c_226,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_223])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:10:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.44  
% 2.36/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.45  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.36/1.45  
% 2.36/1.45  %Foreground sorts:
% 2.36/1.45  
% 2.36/1.45  
% 2.36/1.45  %Background operators:
% 2.36/1.45  
% 2.36/1.45  
% 2.36/1.45  %Foreground operators:
% 2.36/1.45  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.36/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.36/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.36/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.36/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.36/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.36/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.36/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.36/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.36/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.36/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.45  
% 2.36/1.46  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.36/1.46  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 2.36/1.46  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.36/1.46  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 2.36/1.46  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.36/1.46  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 2.36/1.46  tff(f_41, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.36/1.46  tff(c_18, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.46  tff(c_50, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_60, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.46  tff(c_63, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_60])).
% 2.36/1.46  tff(c_66, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_63])).
% 2.36/1.46  tff(c_54, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_48, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_91, plain, (![B_67, A_68]: (k1_funct_1(k2_funct_1(B_67), k1_funct_1(B_67, A_68))=A_68 | ~r2_hidden(A_68, k1_relat_1(B_67)) | ~v2_funct_1(B_67) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.46  tff(c_42, plain, (k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_100, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_91, c_42])).
% 2.36/1.46  tff(c_110, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_48, c_100])).
% 2.36/1.46  tff(c_44, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_52, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_79, plain, (![B_64, A_65, C_66]: (k1_xboole_0=B_64 | k1_relset_1(A_65, B_64, C_66)=A_65 | ~v1_funct_2(C_66, A_65, B_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.36/1.46  tff(c_82, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_79])).
% 2.36/1.46  tff(c_85, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 2.36/1.46  tff(c_86, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_44, c_85])).
% 2.36/1.46  tff(c_46, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.36/1.46  tff(c_174, plain, (![D_95, A_96, B_97, C_98]: (r2_hidden(k4_tarski(D_95, '#skF_6'(A_96, B_97, C_98, D_95)), C_98) | ~r2_hidden(D_95, B_97) | k1_relset_1(B_97, A_96, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(B_97, A_96))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.36/1.46  tff(c_8, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k1_relat_1(A_4)) | ~r2_hidden(k4_tarski(C_19, D_22), A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.46  tff(c_188, plain, (![D_99, C_100, B_101, A_102]: (r2_hidden(D_99, k1_relat_1(C_100)) | ~r2_hidden(D_99, B_101) | k1_relset_1(B_101, A_102, C_100)!=B_101 | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(B_101, A_102))))), inference(resolution, [status(thm)], [c_174, c_8])).
% 2.36/1.46  tff(c_220, plain, (![C_107, A_108]: (r2_hidden('#skF_9', k1_relat_1(C_107)) | k1_relset_1('#skF_7', A_108, C_107)!='#skF_7' | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_7', A_108))))), inference(resolution, [status(thm)], [c_46, c_188])).
% 2.36/1.46  tff(c_223, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10')) | k1_relset_1('#skF_7', '#skF_8', '#skF_10')!='#skF_7'), inference(resolution, [status(thm)], [c_50, c_220])).
% 2.36/1.46  tff(c_226, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_223])).
% 2.36/1.46  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_226])).
% 2.36/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.46  
% 2.36/1.46  Inference rules
% 2.36/1.46  ----------------------
% 2.36/1.46  #Ref     : 0
% 2.36/1.46  #Sup     : 37
% 2.36/1.46  #Fact    : 0
% 2.36/1.46  #Define  : 0
% 2.36/1.46  #Split   : 0
% 2.36/1.46  #Chain   : 0
% 2.36/1.46  #Close   : 0
% 2.36/1.46  
% 2.36/1.46  Ordering : KBO
% 2.36/1.46  
% 2.36/1.46  Simplification rules
% 2.36/1.46  ----------------------
% 2.36/1.46  #Subsume      : 0
% 2.36/1.46  #Demod        : 9
% 2.36/1.46  #Tautology    : 13
% 2.36/1.46  #SimpNegUnit  : 3
% 2.36/1.46  #BackRed      : 0
% 2.36/1.46  
% 2.36/1.46  #Partial instantiations: 0
% 2.36/1.46  #Strategies tried      : 1
% 2.36/1.46  
% 2.36/1.46  Timing (in seconds)
% 2.36/1.46  ----------------------
% 2.36/1.46  Preprocessing        : 0.37
% 2.36/1.46  Parsing              : 0.20
% 2.36/1.46  CNF conversion       : 0.02
% 2.36/1.46  Main loop            : 0.20
% 2.36/1.46  Inferencing          : 0.08
% 2.36/1.46  Reduction            : 0.06
% 2.36/1.46  Demodulation         : 0.04
% 2.36/1.46  BG Simplification    : 0.02
% 2.36/1.46  Subsumption          : 0.04
% 2.36/1.46  Abstraction          : 0.01
% 2.36/1.46  MUC search           : 0.00
% 2.36/1.46  Cooper               : 0.00
% 2.36/1.46  Total                : 0.61
% 2.36/1.46  Index Insertion      : 0.00
% 2.36/1.46  Index Deletion       : 0.00
% 2.36/1.46  Index Matching       : 0.00
% 2.36/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
