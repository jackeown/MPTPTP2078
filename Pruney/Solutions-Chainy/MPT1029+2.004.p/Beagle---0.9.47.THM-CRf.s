%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:48 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 128 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 310 expanded)
%              Number of equality atoms :   24 (  92 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_117,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_99,axiom,(
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

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_176,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_partfun1(C_58,A_59)
      | ~ v1_funct_2(C_58,A_59,B_60)
      | ~ v1_funct_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | v1_xboole_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_182,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_176])).

tff(c_193,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_182])).

tff(c_194,plain,(
    v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_193])).

tff(c_94,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_2'(A_51),A_51)
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(A_51)
      | k1_xboole_0 = A_51 ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_198,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_194,c_98])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_198])).

tff(c_203,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_6])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_205,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_203,c_12])).

tff(c_204,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_211,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_204])).

tff(c_217,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_52])).

tff(c_220,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_217])).

tff(c_272,plain,(
    ! [B_71,A_72] :
      ( v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_281,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_272])).

tff(c_288,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_281])).

tff(c_18,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_251,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_2'(A_68),A_68)
      | A_68 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_18])).

tff(c_255,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(A_68)
      | A_68 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_304,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_288,c_255])).

tff(c_308,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_42])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_228,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_203,c_10])).

tff(c_262,plain,(
    ! [A_70] : m1_subset_1('#skF_3'(A_70),k1_zfmisc_1(k2_zfmisc_1(A_70,A_70))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_266,plain,(
    m1_subset_1('#skF_3'('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_262])).

tff(c_275,plain,
    ( v1_xboole_0('#skF_3'('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_266,c_272])).

tff(c_284,plain,(
    v1_xboole_0('#skF_3'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_275])).

tff(c_318,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_284,c_255])).

tff(c_24,plain,(
    ! [A_36] : v1_partfun1('#skF_3'(A_36),A_36) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_334,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_24])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.15/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.29  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.15/1.29  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.15/1.29  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.15/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.15/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.15/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.15/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.29  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 2.15/1.29  
% 2.15/1.30  tff(f_117, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.15/1.30  tff(f_80, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.15/1.30  tff(f_66, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.15/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.15/1.30  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.30  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.15/1.30  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.15/1.30  tff(f_99, axiom, (![A]: (?[B]: ((((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_relat_2(B)) & v3_relat_2(B)) & v4_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_partfun1)).
% 2.15/1.30  tff(c_44, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.15/1.30  tff(c_70, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 2.15/1.30  tff(c_42, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.15/1.30  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.15/1.30  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.15/1.30  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.15/1.30  tff(c_176, plain, (![C_58, A_59, B_60]: (v1_partfun1(C_58, A_59) | ~v1_funct_2(C_58, A_59, B_60) | ~v1_funct_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | v1_xboole_0(B_60))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.30  tff(c_182, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_176])).
% 2.15/1.30  tff(c_193, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_182])).
% 2.15/1.30  tff(c_194, plain, (v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_193])).
% 2.15/1.30  tff(c_94, plain, (![A_51]: (r2_hidden('#skF_2'(A_51), A_51) | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.30  tff(c_98, plain, (![A_51]: (~v1_xboole_0(A_51) | k1_xboole_0=A_51)), inference(resolution, [status(thm)], [c_94, c_2])).
% 2.15/1.30  tff(c_198, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_194, c_98])).
% 2.15/1.30  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_198])).
% 2.15/1.30  tff(c_203, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.15/1.30  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.30  tff(c_206, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_6])).
% 2.15/1.30  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.30  tff(c_205, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_203, c_12])).
% 2.15/1.30  tff(c_204, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 2.15/1.30  tff(c_211, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_204])).
% 2.15/1.30  tff(c_217, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_52])).
% 2.15/1.30  tff(c_220, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_217])).
% 2.15/1.30  tff(c_272, plain, (![B_71, A_72]: (v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.30  tff(c_281, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_220, c_272])).
% 2.15/1.30  tff(c_288, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_281])).
% 2.15/1.30  tff(c_18, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.30  tff(c_251, plain, (![A_68]: (r2_hidden('#skF_2'(A_68), A_68) | A_68='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_18])).
% 2.15/1.30  tff(c_255, plain, (![A_68]: (~v1_xboole_0(A_68) | A_68='#skF_4')), inference(resolution, [status(thm)], [c_251, c_2])).
% 2.15/1.30  tff(c_304, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_288, c_255])).
% 2.15/1.30  tff(c_308, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_42])).
% 2.15/1.30  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.30  tff(c_228, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_203, c_10])).
% 2.15/1.30  tff(c_262, plain, (![A_70]: (m1_subset_1('#skF_3'(A_70), k1_zfmisc_1(k2_zfmisc_1(A_70, A_70))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.15/1.30  tff(c_266, plain, (m1_subset_1('#skF_3'('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_262])).
% 2.15/1.30  tff(c_275, plain, (v1_xboole_0('#skF_3'('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_266, c_272])).
% 2.15/1.30  tff(c_284, plain, (v1_xboole_0('#skF_3'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_275])).
% 2.15/1.30  tff(c_318, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_284, c_255])).
% 2.15/1.30  tff(c_24, plain, (![A_36]: (v1_partfun1('#skF_3'(A_36), A_36))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.15/1.30  tff(c_334, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_318, c_24])).
% 2.15/1.30  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_334])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 0
% 2.15/1.30  #Sup     : 68
% 2.15/1.30  #Fact    : 0
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 2
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Subsume      : 0
% 2.15/1.30  #Demod        : 38
% 2.15/1.30  #Tautology    : 39
% 2.15/1.30  #SimpNegUnit  : 3
% 2.15/1.30  #BackRed      : 13
% 2.15/1.30  
% 2.15/1.30  #Partial instantiations: 0
% 2.15/1.30  #Strategies tried      : 1
% 2.15/1.30  
% 2.15/1.30  Timing (in seconds)
% 2.15/1.30  ----------------------
% 2.15/1.30  Preprocessing        : 0.31
% 2.15/1.30  Parsing              : 0.16
% 2.15/1.30  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.21
% 2.15/1.30  Inferencing          : 0.07
% 2.15/1.30  Reduction            : 0.07
% 2.15/1.30  Demodulation         : 0.05
% 2.15/1.30  BG Simplification    : 0.01
% 2.15/1.30  Subsumption          : 0.03
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.54
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
