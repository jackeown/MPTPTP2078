%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:04 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  118 ( 269 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
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

tff(f_101,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_59])).

tff(c_65,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_108,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112,plain,(
    v5_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_126,plain,(
    ! [B_75,A_76] :
      ( r2_hidden(k1_funct_1(B_75,A_76),k2_relat_1(B_75))
      | ~ r2_hidden(A_76,k1_relat_1(B_75))
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_177,plain,(
    ! [B_98,A_99,B_100] :
      ( r2_hidden(k1_funct_1(B_98,A_99),B_100)
      | ~ r1_tarski(k2_relat_1(B_98),B_100)
      | ~ r2_hidden(A_99,k1_relat_1(B_98))
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_46,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_182,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_177,c_46])).

tff(c_186,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_56,c_182])).

tff(c_187,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_160,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_163,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_160])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_163])).

tff(c_167,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_166])).

tff(c_50,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_254,plain,(
    ! [D_126,A_127,B_128,C_129] :
      ( r2_hidden(k4_tarski(D_126,'#skF_3'(A_127,B_128,C_129,D_126)),C_129)
      | ~ r2_hidden(D_126,B_128)
      | k1_relset_1(B_128,A_127,C_129) != B_128
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(B_128,A_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_15,C_17,B_16] :
      ( r2_hidden(A_15,k1_relat_1(C_17))
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_435,plain,(
    ! [D_157,C_158,B_159,A_160] :
      ( r2_hidden(D_157,k1_relat_1(C_158))
      | ~ v1_funct_1(C_158)
      | ~ v1_relat_1(C_158)
      | ~ r2_hidden(D_157,B_159)
      | k1_relset_1(B_159,A_160,C_158) != B_159
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(B_159,A_160))) ) ),
    inference(resolution,[status(thm)],[c_254,c_22])).

tff(c_492,plain,(
    ! [C_166,A_167] :
      ( r2_hidden('#skF_6',k1_relat_1(C_166))
      | ~ v1_funct_1(C_166)
      | ~ v1_relat_1(C_166)
      | k1_relset_1('#skF_4',A_167,C_166) != '#skF_4'
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_167))) ) ),
    inference(resolution,[status(thm)],[c_50,c_435])).

tff(c_495,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k1_relset_1('#skF_4','#skF_5','#skF_7') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_492])).

tff(c_498,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_65,c_56,c_495])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_498])).

tff(c_501,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_505,plain,
    ( ~ v5_relat_1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_501])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_112,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.07/1.49  
% 3.07/1.49  %Foreground sorts:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Background operators:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Foreground operators:
% 3.07/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.07/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.07/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.07/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.07/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.07/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.07/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.49  
% 3.07/1.50  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.07/1.50  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.07/1.50  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.07/1.50  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.07/1.50  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.07/1.50  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.07/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.07/1.50  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.07/1.50  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.07/1.50  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.07/1.50  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.50  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.50  tff(c_59, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.50  tff(c_62, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_59])).
% 3.07/1.50  tff(c_65, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 3.07/1.50  tff(c_108, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.50  tff(c_112, plain, (v5_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_108])).
% 3.07/1.50  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.50  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.50  tff(c_126, plain, (![B_75, A_76]: (r2_hidden(k1_funct_1(B_75, A_76), k2_relat_1(B_75)) | ~r2_hidden(A_76, k1_relat_1(B_75)) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.07/1.50  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_177, plain, (![B_98, A_99, B_100]: (r2_hidden(k1_funct_1(B_98, A_99), B_100) | ~r1_tarski(k2_relat_1(B_98), B_100) | ~r2_hidden(A_99, k1_relat_1(B_98)) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_126, c_2])).
% 3.07/1.50  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.50  tff(c_182, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_5') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_177, c_46])).
% 3.07/1.50  tff(c_186, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_5') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_56, c_182])).
% 3.07/1.50  tff(c_187, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_186])).
% 3.07/1.50  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.50  tff(c_54, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.50  tff(c_160, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.07/1.50  tff(c_163, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_160])).
% 3.07/1.50  tff(c_166, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_163])).
% 3.07/1.50  tff(c_167, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_166])).
% 3.07/1.50  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.07/1.50  tff(c_254, plain, (![D_126, A_127, B_128, C_129]: (r2_hidden(k4_tarski(D_126, '#skF_3'(A_127, B_128, C_129, D_126)), C_129) | ~r2_hidden(D_126, B_128) | k1_relset_1(B_128, A_127, C_129)!=B_128 | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(B_128, A_127))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.07/1.50  tff(c_22, plain, (![A_15, C_17, B_16]: (r2_hidden(A_15, k1_relat_1(C_17)) | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.07/1.50  tff(c_435, plain, (![D_157, C_158, B_159, A_160]: (r2_hidden(D_157, k1_relat_1(C_158)) | ~v1_funct_1(C_158) | ~v1_relat_1(C_158) | ~r2_hidden(D_157, B_159) | k1_relset_1(B_159, A_160, C_158)!=B_159 | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(B_159, A_160))))), inference(resolution, [status(thm)], [c_254, c_22])).
% 3.07/1.50  tff(c_492, plain, (![C_166, A_167]: (r2_hidden('#skF_6', k1_relat_1(C_166)) | ~v1_funct_1(C_166) | ~v1_relat_1(C_166) | k1_relset_1('#skF_4', A_167, C_166)!='#skF_4' | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_167))))), inference(resolution, [status(thm)], [c_50, c_435])).
% 3.07/1.50  tff(c_495, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k1_relset_1('#skF_4', '#skF_5', '#skF_7')!='#skF_4'), inference(resolution, [status(thm)], [c_52, c_492])).
% 3.07/1.50  tff(c_498, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_65, c_56, c_495])).
% 3.07/1.50  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_498])).
% 3.07/1.50  tff(c_501, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_186])).
% 3.07/1.50  tff(c_505, plain, (~v5_relat_1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_501])).
% 3.07/1.50  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_112, c_505])).
% 3.07/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  Inference rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Ref     : 0
% 3.07/1.50  #Sup     : 102
% 3.07/1.50  #Fact    : 0
% 3.07/1.50  #Define  : 0
% 3.07/1.50  #Split   : 2
% 3.07/1.50  #Chain   : 0
% 3.07/1.50  #Close   : 0
% 3.07/1.50  
% 3.07/1.50  Ordering : KBO
% 3.07/1.50  
% 3.07/1.50  Simplification rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Subsume      : 15
% 3.07/1.50  #Demod        : 23
% 3.07/1.50  #Tautology    : 14
% 3.07/1.50  #SimpNegUnit  : 3
% 3.07/1.50  #BackRed      : 0
% 3.07/1.50  
% 3.07/1.50  #Partial instantiations: 0
% 3.07/1.50  #Strategies tried      : 1
% 3.07/1.50  
% 3.07/1.50  Timing (in seconds)
% 3.07/1.50  ----------------------
% 3.07/1.50  Preprocessing        : 0.35
% 3.07/1.50  Parsing              : 0.18
% 3.07/1.50  CNF conversion       : 0.02
% 3.07/1.50  Main loop            : 0.35
% 3.07/1.50  Inferencing          : 0.13
% 3.07/1.50  Reduction            : 0.09
% 3.07/1.50  Demodulation         : 0.06
% 3.07/1.50  BG Simplification    : 0.02
% 3.07/1.51  Subsumption          : 0.08
% 3.07/1.51  Abstraction          : 0.01
% 3.07/1.51  MUC search           : 0.00
% 3.07/1.51  Cooper               : 0.00
% 3.07/1.51  Total                : 0.73
% 3.07/1.51  Index Insertion      : 0.00
% 3.07/1.51  Index Deletion       : 0.00
% 3.07/1.51  Index Matching       : 0.00
% 3.07/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
