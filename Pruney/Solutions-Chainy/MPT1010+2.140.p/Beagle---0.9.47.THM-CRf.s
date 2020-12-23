%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 191 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 456 expanded)
%              Number of equality atoms :   24 ( 112 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] : r2_hidden(k4_tarski(A,k1_tarski(A)),k2_zfmisc_1(k1_tarski(A),k4_tarski(A,k1_tarski(A)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_771,plain,(
    ! [D_135,C_136,B_137,A_138] :
      ( r2_hidden(k1_funct_1(D_135,C_136),B_137)
      | k1_xboole_0 = B_137
      | ~ r2_hidden(C_136,A_138)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(D_135,A_138,B_137)
      | ~ v1_funct_1(D_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_887,plain,(
    ! [D_143,B_144] :
      ( r2_hidden(k1_funct_1(D_143,'#skF_9'),B_144)
      | k1_xboole_0 = B_144
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_144)))
      | ~ v1_funct_2(D_143,'#skF_7',B_144)
      | ~ v1_funct_1(D_143) ) ),
    inference(resolution,[status(thm)],[c_50,c_771])).

tff(c_894,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = k1_xboole_0
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_52,c_887])).

tff(c_902,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_894])).

tff(c_904,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_902])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_52,c_24])).

tff(c_905,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_7',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_109])).

tff(c_908,plain,(
    r1_tarski('#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_905])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_990,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_908,c_2])).

tff(c_991,plain,(
    r1_tarski('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_908])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_166,plain,(
    ! [A_71] : r2_hidden(k4_tarski(A_71,k1_tarski(A_71)),k2_zfmisc_1(k1_tarski(A_71),k4_tarski(A_71,k1_tarski(A_71)))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k2_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(D_30,C_27),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,(
    ! [A_72] : r2_hidden(k1_tarski(A_72),k2_relat_1(k2_zfmisc_1(k1_tarski(A_72),k4_tarski(A_72,k1_tarski(A_72))))) ),
    inference(resolution,[status(thm)],[c_166,c_30])).

tff(c_44,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_179,plain,(
    ! [A_72] : ~ r1_tarski(k2_relat_1(k2_zfmisc_1(k1_tarski(A_72),k4_tarski(A_72,k1_tarski(A_72)))),k1_tarski(A_72)) ),
    inference(resolution,[status(thm)],[c_175,c_44])).

tff(c_934,plain,(
    ~ r1_tarski(k2_relat_1(k2_zfmisc_1(k1_xboole_0,k4_tarski('#skF_8',k1_tarski('#skF_8')))),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_179])).

tff(c_977,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_40,c_20,c_934])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_990,c_990,c_977])).

tff(c_1140,plain,(
    r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_902])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1151,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1140,c_4])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.51  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.35/1.51  
% 3.35/1.51  %Foreground sorts:
% 3.35/1.51  
% 3.35/1.51  
% 3.35/1.51  %Background operators:
% 3.35/1.51  
% 3.35/1.51  
% 3.35/1.51  %Foreground operators:
% 3.35/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.35/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.35/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.35/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.35/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.35/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.35/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.35/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.35/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.35/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.35/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.35/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.51  
% 3.35/1.52  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.35/1.52  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.35/1.52  tff(f_76, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.35/1.52  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.35/1.52  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.35/1.52  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.35/1.52  tff(f_44, axiom, (![A]: r2_hidden(k4_tarski(A, k1_tarski(A)), k2_zfmisc_1(k1_tarski(A), k4_tarski(A, k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_zfmisc_1)).
% 3.35/1.52  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.35/1.52  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.35/1.52  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.35/1.52  tff(c_48, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.35/1.52  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.52  tff(c_56, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.35/1.52  tff(c_54, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.35/1.52  tff(c_52, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.35/1.52  tff(c_50, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.35/1.52  tff(c_771, plain, (![D_135, C_136, B_137, A_138]: (r2_hidden(k1_funct_1(D_135, C_136), B_137) | k1_xboole_0=B_137 | ~r2_hidden(C_136, A_138) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(D_135, A_138, B_137) | ~v1_funct_1(D_135))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.35/1.52  tff(c_887, plain, (![D_143, B_144]: (r2_hidden(k1_funct_1(D_143, '#skF_9'), B_144) | k1_xboole_0=B_144 | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_144))) | ~v1_funct_2(D_143, '#skF_7', B_144) | ~v1_funct_1(D_143))), inference(resolution, [status(thm)], [c_50, c_771])).
% 3.35/1.52  tff(c_894, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_tarski('#skF_8')) | k1_tarski('#skF_8')=k1_xboole_0 | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8')) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_52, c_887])).
% 3.35/1.52  tff(c_902, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_tarski('#skF_8')) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_894])).
% 3.35/1.52  tff(c_904, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_902])).
% 3.35/1.52  tff(c_24, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.35/1.52  tff(c_109, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_52, c_24])).
% 3.35/1.52  tff(c_905, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_7', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_904, c_109])).
% 3.35/1.52  tff(c_908, plain, (r1_tarski('#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_905])).
% 3.35/1.52  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.52  tff(c_990, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_908, c_2])).
% 3.35/1.52  tff(c_991, plain, (r1_tarski('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_990, c_908])).
% 3.35/1.52  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.35/1.52  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.52  tff(c_166, plain, (![A_71]: (r2_hidden(k4_tarski(A_71, k1_tarski(A_71)), k2_zfmisc_1(k1_tarski(A_71), k4_tarski(A_71, k1_tarski(A_71)))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.35/1.52  tff(c_30, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k2_relat_1(A_12)) | ~r2_hidden(k4_tarski(D_30, C_27), A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.52  tff(c_175, plain, (![A_72]: (r2_hidden(k1_tarski(A_72), k2_relat_1(k2_zfmisc_1(k1_tarski(A_72), k4_tarski(A_72, k1_tarski(A_72))))))), inference(resolution, [status(thm)], [c_166, c_30])).
% 3.35/1.52  tff(c_44, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.52  tff(c_179, plain, (![A_72]: (~r1_tarski(k2_relat_1(k2_zfmisc_1(k1_tarski(A_72), k4_tarski(A_72, k1_tarski(A_72)))), k1_tarski(A_72)))), inference(resolution, [status(thm)], [c_175, c_44])).
% 3.35/1.52  tff(c_934, plain, (~r1_tarski(k2_relat_1(k2_zfmisc_1(k1_xboole_0, k4_tarski('#skF_8', k1_tarski('#skF_8')))), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_904, c_179])).
% 3.35/1.52  tff(c_977, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_904, c_40, c_20, c_934])).
% 3.35/1.52  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_991, c_990, c_990, c_977])).
% 3.35/1.52  tff(c_1140, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_902])).
% 3.35/1.52  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.35/1.52  tff(c_1151, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_1140, c_4])).
% 3.35/1.52  tff(c_1158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1151])).
% 3.35/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.52  
% 3.35/1.52  Inference rules
% 3.35/1.52  ----------------------
% 3.35/1.52  #Ref     : 0
% 3.35/1.52  #Sup     : 262
% 3.35/1.52  #Fact    : 0
% 3.35/1.52  #Define  : 0
% 3.35/1.52  #Split   : 3
% 3.35/1.52  #Chain   : 0
% 3.35/1.52  #Close   : 0
% 3.35/1.52  
% 3.35/1.52  Ordering : KBO
% 3.35/1.52  
% 3.35/1.52  Simplification rules
% 3.35/1.52  ----------------------
% 3.35/1.52  #Subsume      : 21
% 3.35/1.52  #Demod        : 182
% 3.35/1.52  #Tautology    : 49
% 3.35/1.52  #SimpNegUnit  : 1
% 3.35/1.52  #BackRed      : 21
% 3.35/1.52  
% 3.35/1.52  #Partial instantiations: 0
% 3.35/1.52  #Strategies tried      : 1
% 3.35/1.52  
% 3.35/1.52  Timing (in seconds)
% 3.35/1.52  ----------------------
% 3.35/1.52  Preprocessing        : 0.30
% 3.35/1.52  Parsing              : 0.16
% 3.35/1.52  CNF conversion       : 0.02
% 3.35/1.52  Main loop            : 0.47
% 3.35/1.52  Inferencing          : 0.16
% 3.35/1.52  Reduction            : 0.15
% 3.35/1.52  Demodulation         : 0.11
% 3.35/1.52  BG Simplification    : 0.02
% 3.35/1.52  Subsumption          : 0.09
% 3.35/1.52  Abstraction          : 0.02
% 3.35/1.52  MUC search           : 0.00
% 3.35/1.52  Cooper               : 0.00
% 3.35/1.52  Total                : 0.79
% 3.35/1.52  Index Insertion      : 0.00
% 3.35/1.52  Index Deletion       : 0.00
% 3.35/1.52  Index Matching       : 0.00
% 3.35/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
