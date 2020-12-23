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
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 121 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 280 expanded)
%              Number of equality atoms :   23 (  90 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_86,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_relat_2(B)
      & v3_relat_2(B)
      & v4_relat_2(B)
      & v8_relat_2(B)
      & v1_partfun1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_partfun1)).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_183,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_partfun1(C_40,A_41)
      | ~ v1_funct_2(C_40,A_41,B_42)
      | ~ v1_funct_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_189,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_183])).

tff(c_200,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_189])).

tff(c_201,plain,(
    v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_200])).

tff(c_87,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_2'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_205,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_201,c_91])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_205])).

tff(c_210,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_258,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_8])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_225,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_210,c_12])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_217,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_211])).

tff(c_223,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_50])).

tff(c_226,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_223])).

tff(c_292,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_298,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_226,c_292])).

tff(c_306,plain,(
    ! [A_59] : ~ r2_hidden(A_59,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_298])).

tff(c_315,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_258,c_306])).

tff(c_320,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_40])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_234,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_210,c_14])).

tff(c_270,plain,(
    ! [A_53] : m1_subset_1('#skF_3'(A_53),k1_zfmisc_1(k2_zfmisc_1(A_53,A_53))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_274,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_270])).

tff(c_294,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_58,'#skF_3'('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_274,c_292])).

tff(c_340,plain,(
    ! [A_61] : ~ r2_hidden(A_61,'#skF_3'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_294])).

tff(c_349,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_258,c_340])).

tff(c_22,plain,(
    ! [A_16] : v1_partfun1('#skF_3'(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_359,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_22])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.25  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.20/1.25  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.20/1.25  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.20/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.20/1.25  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.20/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.20/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.25  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.25  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 2.20/1.25  
% 2.20/1.26  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.20/1.26  tff(f_67, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.20/1.26  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.20/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.26  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.20/1.26  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.20/1.26  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.20/1.26  tff(f_86, axiom, (![A]: (?[B]: ((((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_relat_2(B)) & v3_relat_2(B)) & v4_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_partfun1)).
% 2.20/1.26  tff(c_42, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.20/1.26  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 2.20/1.26  tff(c_40, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.20/1.26  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.20/1.26  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.20/1.26  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.20/1.26  tff(c_183, plain, (![C_40, A_41, B_42]: (v1_partfun1(C_40, A_41) | ~v1_funct_2(C_40, A_41, B_42) | ~v1_funct_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.20/1.26  tff(c_189, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_183])).
% 2.20/1.26  tff(c_200, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_189])).
% 2.20/1.26  tff(c_201, plain, (v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_200])).
% 2.20/1.26  tff(c_87, plain, (![A_30]: (r2_hidden('#skF_2'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.26  tff(c_91, plain, (![A_30]: (~v1_xboole_0(A_30) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.20/1.26  tff(c_205, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_201, c_91])).
% 2.20/1.26  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_205])).
% 2.20/1.26  tff(c_210, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.20/1.26  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.26  tff(c_258, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_8])).
% 2.20/1.26  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.26  tff(c_212, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_6])).
% 2.20/1.26  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.26  tff(c_225, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_210, c_12])).
% 2.20/1.26  tff(c_211, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.20/1.26  tff(c_217, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_211])).
% 2.20/1.26  tff(c_223, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_50])).
% 2.20/1.26  tff(c_226, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_223])).
% 2.20/1.26  tff(c_292, plain, (![C_56, B_57, A_58]: (~v1_xboole_0(C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.26  tff(c_298, plain, (![A_58]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_58, '#skF_6'))), inference(resolution, [status(thm)], [c_226, c_292])).
% 2.20/1.26  tff(c_306, plain, (![A_59]: (~r2_hidden(A_59, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_298])).
% 2.20/1.26  tff(c_315, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_258, c_306])).
% 2.20/1.26  tff(c_320, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_40])).
% 2.20/1.26  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.26  tff(c_234, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_210, c_14])).
% 2.20/1.26  tff(c_270, plain, (![A_53]: (m1_subset_1('#skF_3'(A_53), k1_zfmisc_1(k2_zfmisc_1(A_53, A_53))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_274, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_270])).
% 2.20/1.26  tff(c_294, plain, (![A_58]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_58, '#skF_3'('#skF_4')))), inference(resolution, [status(thm)], [c_274, c_292])).
% 2.20/1.26  tff(c_340, plain, (![A_61]: (~r2_hidden(A_61, '#skF_3'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_294])).
% 2.20/1.26  tff(c_349, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_258, c_340])).
% 2.20/1.26  tff(c_22, plain, (![A_16]: (v1_partfun1('#skF_3'(A_16), A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_359, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_349, c_22])).
% 2.20/1.26  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_359])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 74
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 2
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 1
% 2.20/1.26  #Demod        : 40
% 2.20/1.26  #Tautology    : 40
% 2.20/1.26  #SimpNegUnit  : 3
% 2.20/1.26  #BackRed      : 13
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.27  Preprocessing        : 0.30
% 2.20/1.27  Parsing              : 0.16
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.20
% 2.20/1.27  Inferencing          : 0.07
% 2.20/1.27  Reduction            : 0.07
% 2.20/1.27  Demodulation         : 0.05
% 2.20/1.27  BG Simplification    : 0.01
% 2.20/1.27  Subsumption          : 0.03
% 2.20/1.27  Abstraction          : 0.01
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.53
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
