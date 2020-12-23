%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 582 expanded)
%              Number of leaves         :   24 ( 200 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 (1330 expanded)
%              Number of equality atoms :   48 ( 299 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_79,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34])).

tff(c_36,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_147,plain,(
    ! [B_45,C_46,A_47] :
      ( k1_xboole_0 = B_45
      | v1_funct_2(C_46,A_47,B_45)
      | k1_relset_1(A_47,B_45,C_46) != A_47
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_147])).

tff(c_163,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_150])).

tff(c_164,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_163])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_175,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_164,c_12])).

tff(c_103,plain,(
    ! [C_31,B_32,A_33] :
      ( ~ v1_xboole_0(C_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_33,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_103])).

tff(c_125,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_213,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_125])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_213])).

tff(c_219,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,(
    ! [A_53] : ~ r2_hidden(A_53,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_225,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_220])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_266,plain,(
    ! [A_58] :
      ( A_58 = '#skF_4'
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_273,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_219,c_266])).

tff(c_82,plain,(
    ! [B_26,A_27] :
      ( ~ v1_xboole_0(B_26)
      | B_26 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_231,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_225,c_85])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_311,plain,(
    ! [B_63,A_64] :
      ( B_63 = '#skF_4'
      | A_64 = '#skF_4'
      | k2_zfmisc_1(A_64,B_63) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_231,c_231,c_10])).

tff(c_321,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_311])).

tff(c_326,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_328,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_36])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_239,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_16])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_45,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_299,plain,(
    ! [C_60,B_61] :
      ( v1_funct_2(C_60,'#skF_4',B_61)
      | k1_relset_1('#skF_4',B_61,C_60) != '#skF_4'
      | ~ m1_subset_1(C_60,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_231,c_231,c_231,c_45])).

tff(c_339,plain,(
    ! [B_65] :
      ( v1_funct_2('#skF_4','#skF_4',B_65)
      | k1_relset_1('#skF_4',B_65,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_239,c_299])).

tff(c_329,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_42])).

tff(c_342,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_339,c_329])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_342])).

tff(c_351,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_22,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_236,plain,(
    ! [A_16] :
      ( v1_funct_2('#skF_4',A_16,'#skF_4')
      | A_16 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_231,c_231,c_44])).

tff(c_350,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_354,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_42])).

tff(c_371,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_236,c_354])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.42  
% 2.39/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.39/1.42  
% 2.39/1.42  %Foreground sorts:
% 2.39/1.42  
% 2.39/1.42  
% 2.39/1.42  %Background operators:
% 2.39/1.42  
% 2.39/1.42  
% 2.39/1.42  %Foreground operators:
% 2.39/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.39/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.39/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.42  
% 2.39/1.43  tff(f_92, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.39/1.43  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.39/1.43  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.39/1.43  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.39/1.43  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.39/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.39/1.43  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.39/1.43  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.39/1.43  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.39/1.43  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.39/1.43  tff(c_34, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.39/1.43  tff(c_42, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34])).
% 2.39/1.43  tff(c_36, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.39/1.43  tff(c_147, plain, (![B_45, C_46, A_47]: (k1_xboole_0=B_45 | v1_funct_2(C_46, A_47, B_45) | k1_relset_1(A_47, B_45, C_46)!=A_47 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_45))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.43  tff(c_150, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_38, c_147])).
% 2.39/1.43  tff(c_163, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_150])).
% 2.39/1.43  tff(c_164, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_42, c_163])).
% 2.39/1.43  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.43  tff(c_178, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_6])).
% 2.39/1.43  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.43  tff(c_175, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_164, c_12])).
% 2.39/1.43  tff(c_103, plain, (![C_31, B_32, A_33]: (~v1_xboole_0(C_31) | ~m1_subset_1(B_32, k1_zfmisc_1(C_31)) | ~r2_hidden(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.39/1.43  tff(c_108, plain, (![A_33]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_33, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_103])).
% 2.39/1.43  tff(c_125, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_108])).
% 2.39/1.43  tff(c_213, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_125])).
% 2.39/1.43  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_213])).
% 2.39/1.43  tff(c_219, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_108])).
% 2.39/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.43  tff(c_220, plain, (![A_53]: (~r2_hidden(A_53, '#skF_4'))), inference(splitRight, [status(thm)], [c_108])).
% 2.39/1.43  tff(c_225, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_220])).
% 2.39/1.43  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.39/1.43  tff(c_266, plain, (![A_58]: (A_58='#skF_4' | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_225, c_8])).
% 2.39/1.43  tff(c_273, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_219, c_266])).
% 2.39/1.43  tff(c_82, plain, (![B_26, A_27]: (~v1_xboole_0(B_26) | B_26=A_27 | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.39/1.43  tff(c_85, plain, (![A_27]: (k1_xboole_0=A_27 | ~v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.39/1.43  tff(c_231, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_225, c_85])).
% 2.39/1.43  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.43  tff(c_311, plain, (![B_63, A_64]: (B_63='#skF_4' | A_64='#skF_4' | k2_zfmisc_1(A_64, B_63)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_231, c_231, c_10])).
% 2.39/1.43  tff(c_321, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_273, c_311])).
% 2.39/1.43  tff(c_326, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_321])).
% 2.39/1.43  tff(c_328, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_36])).
% 2.39/1.43  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.39/1.43  tff(c_239, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_16])).
% 2.39/1.43  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.43  tff(c_26, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.43  tff(c_45, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 2.39/1.43  tff(c_299, plain, (![C_60, B_61]: (v1_funct_2(C_60, '#skF_4', B_61) | k1_relset_1('#skF_4', B_61, C_60)!='#skF_4' | ~m1_subset_1(C_60, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_231, c_231, c_231, c_45])).
% 2.39/1.43  tff(c_339, plain, (![B_65]: (v1_funct_2('#skF_4', '#skF_4', B_65) | k1_relset_1('#skF_4', B_65, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_239, c_299])).
% 2.39/1.43  tff(c_329, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_42])).
% 2.39/1.43  tff(c_342, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_339, c_329])).
% 2.39/1.43  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_328, c_342])).
% 2.39/1.43  tff(c_351, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_321])).
% 2.39/1.43  tff(c_22, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.43  tff(c_44, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.39/1.43  tff(c_236, plain, (![A_16]: (v1_funct_2('#skF_4', A_16, '#skF_4') | A_16='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_231, c_231, c_44])).
% 2.39/1.43  tff(c_350, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_321])).
% 2.39/1.43  tff(c_354, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_42])).
% 2.39/1.43  tff(c_371, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_236, c_354])).
% 2.39/1.43  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_351, c_371])).
% 2.39/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.43  
% 2.39/1.43  Inference rules
% 2.39/1.43  ----------------------
% 2.39/1.43  #Ref     : 0
% 2.39/1.43  #Sup     : 66
% 2.39/1.43  #Fact    : 0
% 2.39/1.43  #Define  : 0
% 2.39/1.43  #Split   : 3
% 2.39/1.43  #Chain   : 0
% 2.39/1.43  #Close   : 0
% 2.39/1.43  
% 2.39/1.43  Ordering : KBO
% 2.39/1.43  
% 2.39/1.43  Simplification rules
% 2.39/1.43  ----------------------
% 2.39/1.43  #Subsume      : 11
% 2.39/1.43  #Demod        : 87
% 2.39/1.43  #Tautology    : 45
% 2.39/1.43  #SimpNegUnit  : 2
% 2.39/1.43  #BackRed      : 30
% 2.39/1.43  
% 2.39/1.43  #Partial instantiations: 0
% 2.39/1.43  #Strategies tried      : 1
% 2.39/1.43  
% 2.39/1.43  Timing (in seconds)
% 2.39/1.43  ----------------------
% 2.39/1.44  Preprocessing        : 0.32
% 2.39/1.44  Parsing              : 0.17
% 2.39/1.44  CNF conversion       : 0.02
% 2.39/1.44  Main loop            : 0.25
% 2.39/1.44  Inferencing          : 0.08
% 2.39/1.44  Reduction            : 0.08
% 2.39/1.44  Demodulation         : 0.06
% 2.39/1.44  BG Simplification    : 0.02
% 2.39/1.44  Subsumption          : 0.05
% 2.39/1.44  Abstraction          : 0.01
% 2.39/1.44  MUC search           : 0.00
% 2.39/1.44  Cooper               : 0.00
% 2.39/1.44  Total                : 0.61
% 2.39/1.44  Index Insertion      : 0.00
% 2.39/1.44  Index Deletion       : 0.00
% 2.39/1.44  Index Matching       : 0.00
% 2.39/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
