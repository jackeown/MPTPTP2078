%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 454 expanded)
%              Number of leaves         :   23 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 (1182 expanded)
%              Number of equality atoms :   43 ( 317 expanded)
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

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_73,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30])).

tff(c_32,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_115,plain,(
    ! [B_32,C_33,A_34] :
      ( k1_xboole_0 = B_32
      | v1_funct_2(C_33,A_34,B_32)
      | k1_relset_1(A_34,B_32,C_33) != A_34
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_115])).

tff(c_131,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_118])).

tff(c_132,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_131])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_144,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_141,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_8])).

tff(c_84,plain,(
    ! [C_22,B_23,A_24] :
      ( ~ v1_xboole_0(C_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_99,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_167,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_99])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_167])).

tff(c_174,plain,(
    ! [A_40] : ~ r2_hidden(A_40,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_funct_2(k1_xboole_0,A_12,k1_xboole_0)
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_12,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_12] :
      ( v1_funct_2(k1_xboole_0,A_12,k1_xboole_0)
      | k1_xboole_0 = A_12 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_181,plain,(
    ! [A_12] :
      ( v1_funct_2('#skF_4',A_12,'#skF_4')
      | A_12 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_179,c_40])).

tff(c_186,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_12])).

tff(c_24,plain,(
    ! [B_13,C_14,A_12] :
      ( k1_xboole_0 = B_13
      | v1_funct_2(C_14,A_12,B_13)
      | k1_relset_1(A_12,B_13,C_14) != A_12
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_303,plain,(
    ! [B_63,C_64,A_65] :
      ( B_63 = '#skF_4'
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_24])).

tff(c_316,plain,(
    ! [B_66,A_67] :
      ( B_66 = '#skF_4'
      | v1_funct_2('#skF_4',A_67,B_66)
      | k1_relset_1(A_67,B_66,'#skF_4') != A_67 ) ),
    inference(resolution,[status(thm)],[c_186,c_303])).

tff(c_328,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_316,c_38])).

tff(c_339,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_328])).

tff(c_342,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_38])).

tff(c_356,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_181,c_342])).

tff(c_341,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_32])).

tff(c_361,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_356,c_341])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [C_14,B_13] :
      ( v1_funct_2(C_14,k1_xboole_0,B_13)
      | k1_relset_1(k1_xboole_0,B_13,C_14) != k1_xboole_0
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_41,plain,(
    ! [C_14,B_13] :
      ( v1_funct_2(C_14,k1_xboole_0,B_13)
      | k1_relset_1(k1_xboole_0,B_13,C_14) != k1_xboole_0
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_280,plain,(
    ! [C_60,B_61] :
      ( v1_funct_2(C_60,'#skF_4',B_61)
      | k1_relset_1('#skF_4',B_61,C_60) != '#skF_4'
      | ~ m1_subset_1(C_60,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_179,c_179,c_41])).

tff(c_284,plain,(
    ! [B_61] :
      ( v1_funct_2('#skF_4','#skF_4',B_61)
      | k1_relset_1('#skF_4',B_61,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_186,c_280])).

tff(c_362,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_342])).

tff(c_378,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_284,c_362])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.34  
% 2.23/1.35  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.23/1.35  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.23/1.35  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.23/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.35  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.23/1.35  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.23/1.35  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.23/1.35  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.35  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_30, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_38, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30])).
% 2.23/1.35  tff(c_32, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.23/1.35  tff(c_115, plain, (![B_32, C_33, A_34]: (k1_xboole_0=B_32 | v1_funct_2(C_33, A_34, B_32) | k1_relset_1(A_34, B_32, C_33)!=A_34 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_32))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.35  tff(c_118, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_34, c_115])).
% 2.23/1.35  tff(c_131, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_118])).
% 2.23/1.35  tff(c_132, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_131])).
% 2.23/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.35  tff(c_144, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_2])).
% 2.23/1.35  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.35  tff(c_141, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_8])).
% 2.23/1.35  tff(c_84, plain, (![C_22, B_23, A_24]: (~v1_xboole_0(C_22) | ~m1_subset_1(B_23, k1_zfmisc_1(C_22)) | ~r2_hidden(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.35  tff(c_89, plain, (![A_24]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_24, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_84])).
% 2.23/1.35  tff(c_99, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_89])).
% 2.23/1.35  tff(c_167, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_99])).
% 2.23/1.35  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_167])).
% 2.23/1.35  tff(c_174, plain, (![A_40]: (~r2_hidden(A_40, '#skF_4'))), inference(splitRight, [status(thm)], [c_89])).
% 2.23/1.35  tff(c_179, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_174])).
% 2.23/1.35  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.35  tff(c_18, plain, (![A_12]: (v1_funct_2(k1_xboole_0, A_12, k1_xboole_0) | k1_xboole_0=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_12, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.35  tff(c_40, plain, (![A_12]: (v1_funct_2(k1_xboole_0, A_12, k1_xboole_0) | k1_xboole_0=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 2.23/1.35  tff(c_181, plain, (![A_12]: (v1_funct_2('#skF_4', A_12, '#skF_4') | A_12='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_179, c_40])).
% 2.23/1.35  tff(c_186, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_12])).
% 2.23/1.35  tff(c_24, plain, (![B_13, C_14, A_12]: (k1_xboole_0=B_13 | v1_funct_2(C_14, A_12, B_13) | k1_relset_1(A_12, B_13, C_14)!=A_12 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.35  tff(c_303, plain, (![B_63, C_64, A_65]: (B_63='#skF_4' | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_24])).
% 2.23/1.35  tff(c_316, plain, (![B_66, A_67]: (B_66='#skF_4' | v1_funct_2('#skF_4', A_67, B_66) | k1_relset_1(A_67, B_66, '#skF_4')!=A_67)), inference(resolution, [status(thm)], [c_186, c_303])).
% 2.23/1.35  tff(c_328, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_316, c_38])).
% 2.23/1.35  tff(c_339, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_328])).
% 2.23/1.35  tff(c_342, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_38])).
% 2.23/1.35  tff(c_356, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_181, c_342])).
% 2.23/1.35  tff(c_341, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_339, c_32])).
% 2.23/1.35  tff(c_361, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_356, c_341])).
% 2.23/1.35  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.35  tff(c_22, plain, (![C_14, B_13]: (v1_funct_2(C_14, k1_xboole_0, B_13) | k1_relset_1(k1_xboole_0, B_13, C_14)!=k1_xboole_0 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.35  tff(c_41, plain, (![C_14, B_13]: (v1_funct_2(C_14, k1_xboole_0, B_13) | k1_relset_1(k1_xboole_0, B_13, C_14)!=k1_xboole_0 | ~m1_subset_1(C_14, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 2.23/1.35  tff(c_280, plain, (![C_60, B_61]: (v1_funct_2(C_60, '#skF_4', B_61) | k1_relset_1('#skF_4', B_61, C_60)!='#skF_4' | ~m1_subset_1(C_60, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_179, c_179, c_41])).
% 2.23/1.35  tff(c_284, plain, (![B_61]: (v1_funct_2('#skF_4', '#skF_4', B_61) | k1_relset_1('#skF_4', B_61, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_186, c_280])).
% 2.23/1.35  tff(c_362, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_342])).
% 2.23/1.35  tff(c_378, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_284, c_362])).
% 2.23/1.35  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_361, c_378])).
% 2.23/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  Inference rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Ref     : 0
% 2.23/1.35  #Sup     : 70
% 2.23/1.35  #Fact    : 0
% 2.23/1.35  #Define  : 0
% 2.23/1.35  #Split   : 2
% 2.23/1.35  #Chain   : 0
% 2.23/1.35  #Close   : 0
% 2.23/1.35  
% 2.23/1.35  Ordering : KBO
% 2.23/1.35  
% 2.23/1.35  Simplification rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Subsume      : 8
% 2.23/1.35  #Demod        : 80
% 2.23/1.35  #Tautology    : 52
% 2.23/1.35  #SimpNegUnit  : 1
% 2.23/1.35  #BackRed      : 26
% 2.23/1.35  
% 2.23/1.35  #Partial instantiations: 0
% 2.23/1.35  #Strategies tried      : 1
% 2.23/1.35  
% 2.23/1.35  Timing (in seconds)
% 2.23/1.35  ----------------------
% 2.23/1.36  Preprocessing        : 0.32
% 2.23/1.36  Parsing              : 0.18
% 2.23/1.36  CNF conversion       : 0.02
% 2.23/1.36  Main loop            : 0.24
% 2.23/1.36  Inferencing          : 0.08
% 2.23/1.36  Reduction            : 0.08
% 2.23/1.36  Demodulation         : 0.05
% 2.23/1.36  BG Simplification    : 0.02
% 2.23/1.36  Subsumption          : 0.05
% 2.23/1.36  Abstraction          : 0.01
% 2.23/1.36  MUC search           : 0.00
% 2.23/1.36  Cooper               : 0.00
% 2.23/1.36  Total                : 0.59
% 2.23/1.36  Index Insertion      : 0.00
% 2.23/1.36  Index Deletion       : 0.00
% 2.23/1.36  Index Matching       : 0.00
% 2.23/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
